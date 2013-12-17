import os
import sys
import logging
import argparse

from elftools.elf.elffile import ELFFile
from elftools.elf.constants import P_FLAGS
from disassembler.arch import ARMRegister, ARMMode, \
    InstructionNotImplementedException
from emulator.memory import ConcreteMemoryMap, GetLastValidAddress, \
    InvalidMemoryAccessException, MemoryMapIterator
from emulator.ARMEmulator import ARMEmulator
from disassembler.utils.bits import Align
from collections import namedtuple
from emulator.syscalls import *

__author__ = 'anon'

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("executor")

PF_R = 0x4
PF_W = 0x2
PF_X = 0x1

PROT_NONE = 0x00
PROT_READ = 0x01
PROT_WRITE = 0x02
PROT_EXEC = 0x04

MAP_SHARED = 0x001
MAP_PRIVATE = 0x002
MAP_TYPE = 0x00f
MAP_FIXED = 0x010
MAP_EXECUTABLE = 0x4000

# Symbolic values for the entries in the auxiliary table
AT_NULL = 0  # end of vector
AT_IGNORE = 1  # entry should be ignored
AT_EXECFD = 2  # file descriptor of program
AT_PHDR = 3  # program headers for program
AT_PHENT = 4  # size of program header entry
AT_PHNUM = 5  # number of program headers
AT_PAGESZ = 6  # system page size
AT_BASE = 7  # base address of interpreter
AT_FLAGS = 8  # flags
AT_ENTRY = 9  # entry point of program
AT_NOTELF = 10  # program is not ELF
AT_UID = 11  # real uid
AT_EUID = 12  # effective uid
AT_GID = 13  # real gid
AT_EGID = 14  # effective gid
AT_PLATFORM = 15  # string identifying CPU for optimizations
AT_HWCAP = 16  # arch dependent hints at CPU capabilities
AT_CLKTCK = 17  # frequency at which times() increments
AT_SECURE = 23  # secure mode boolean
AT_BASE_PLATFORM = 24  # string identifying real platform, may differ from AT_PLATFORM.
AT_RANDOM = 25  # address of 16 random bytes
AT_EXECFN = 31  # filename of program


def MAP_TO_DESC(x):
    names = []
    if x & MAP_SHARED:
        names.append("s")
    else:
        names.append("-")

    if x & MAP_PRIVATE:
        names.append("p")
    else:
        names.append("-")

    if x & MAP_FIXED:
        names.append("f")
    else:
        names.append("-")

    if x & MAP_EXECUTABLE:
        names.append("e")
    else:
        names.append("-")

    return "".join(names)


def PROT_TO_NAME(x):
    names = []
    if x & PROT_READ:
        names.append("PROT_READ")

    if x & PROT_WRITE:
        names.append("PROT_WRITE")

    if x & PROT_EXEC:
        names.append("PROT_EXEC")

    return " | ".join(names)


def PROT_TO_DESC(x):
    names = []
    if x & PROT_READ:
        names.append("r")
    else:
        names.append("-")

    if x & PROT_WRITE:
        names.append("w")
    else:
        names.append("-")

    if x & PROT_EXEC:
        names.append("e")
    else:
        names.append("-")

    return "".join(names)


def PFLAGS_TO_PROT(x):
    prot = 0
    if x & P_FLAGS.PF_X:
        prot |= PROT_EXEC

    if x & P_FLAGS.PF_R:
        prot |= PROT_READ

    if x & P_FLAGS.PF_W:
        prot |= PROT_WRITE

    return prot


PAGE_SHIFT = 12
PAGE_SIZE = 1 << PAGE_SHIFT
PAGE_MASK = ~(PAGE_SIZE - 1)


def PAGE_ALIGN(x):
    return (x + PAGE_SIZE - 1) & PAGE_MASK


def PAGE_START(x):
    return x & PAGE_MASK


def PAGE_OFFSET(x):
    return x & ~PAGE_MASK


def PAGE_END(x):
    return PAGE_START(x + (PAGE_SIZE - 1))


class File(object):
    def __init__(self, filename, flags):
        if flags & os.O_RDONLY:
            mode = "rb"
        elif flags & os.O_WRONLY:
            mode = "wb"
        elif flags & os.O_RDWR:
            mode = "wb+"
        else:
            raise RuntimeError("Invalid open mode %.8x" % flags)
            
        self.file = os.fdopen(os.open(filename, flags), mode)

    def stat(self):
        return os.fstat(self.fileno())

    def ioctl(self, request):
        import fcntl
        return fcntl.fcntl(self, request)

    @property
    def name(self):
        return self.file.name

    @property
    def mode(self):
        return self.file.mode

    def tell(self, *args):
        return self.file.tell(*args)

    def seek(self, *args):
        return self.file.seek(*args)

    def write(self, *args):
        return self.file.write(*args)

    def read(self, *args):
        return self.file.read(*args)

    def close(self, *args):
        return self.file.close(*args)

    def fileno(self, *args):
        return self.file.fileno(*args)

    def __getstate__(self):
        state = {}
        state['name'] = self.name
        state['mode'] = self.mode
        state['pos'] = self.tell()
        return state

    def __setstate__(self, state):
        name = state['name']
        mode = state['mode']
        pos = state['pos']
        self.file = file(name, mode)
        self.seek(pos)


class Task(object):
    def __init__(self, memory):
        self.files = []
        self.memory = memory


class MissingSyscallException(Exception):
    pass

class EmulationExited(Exception):
    pass

class LinuxOS(object):
    def __init__(self, cpu, memory):
        """
        Emulate the behaviour of the Linux OS.

        The are platform specific bits should be implemented by inheriting
        this class and overriding the proper abstract methods.
        
        Some of the syscalls can be implemented on this class due to their platform
        independency. Other syscalls should be implemented in platform specific classes.
        """
        # Set up the basic elements of the virtual machine.
        self.cpu = cpu

        # List of file descriptors
        self.files = []

        # This is a map of all the tasks being executed.
        self.tasks = {}
        self.curr_task = Task(memory)
        
        self.elf_brk = 0

    def get_current_task(self):
        """
        Return the current running task.
        """
        return self.curr_task

    def set_current_task(self, task):
        """
        Set the current task.
        """
        self.curr_task = task

    def __do_mmap__(self, filep, addr, size, prot, type_, off):
        """
        Wrapper over mmap. This is to follow the binfmt_elf.c way of mapping
        segments.
        """
        return self.sys_mmap(addr, size, prot, type_, filep, off)

    def __elf_map__(self, filep, addr, eppnt, prot, type_, total_size):
        size = eppnt.header.p_filesz + PAGE_OFFSET(eppnt.header.p_vaddr)
        off = eppnt.header.p_offset - PAGE_OFFSET(eppnt.header.p_vaddr)

        addr = PAGE_START(addr)
        size = PAGE_ALIGN(size)

        if not size:
            return addr

        if total_size:
            total_size = PAGE_ALIGN(total_size)
            map_addr = self.__do_mmap__(filep, addr, total_size, prot, type_, off)

        else:
            map_addr = self.__do_mmap__(filep, addr, size, prot, type_, off)

        return map_addr

    def __set_brk__(self, start, end):
        """
        Allocate memory for the brk.
        """
        start = PAGE_ALIGN(start)
        end = PAGE_ALIGN(end)
        if end <= start:
            return -1

        return self.sys_mmap(start, end - start, PROT_READ | PROT_WRITE, MAP_FIXED | MAP_PRIVATE, 0, 0)

    def __load_elf_interp__(self, elf, interpreter, no_base=None):
        load_addr = 0
        load_addr_set = 0
        last_bss = 0
        elf_bss = 0

        # Get the total size of the binary by substracting the first and last segment.
        first = None
        last = None

        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type == 'PT_LOAD':
                last = elf_segment

                if not first:
                    first = elf_segment

        total_size = last.header.p_vaddr + last.header.p_memsz - PAGE_START(first.header.p_vaddr)

        # For each loadable segment.
        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != 'PT_LOAD':
                continue

            # Default protection for the interpreter.
            elf_type = MAP_PRIVATE
            elf_prot = 0

            # Decode protection.
            if elf_segment.header.p_flags & PF_R:
                elf_prot |= PROT_READ

            if elf_segment.header.p_flags & PF_W:
                elf_prot |= PROT_WRITE

            if elf_segment.header.p_flags & PF_X:
                elf_prot |= PROT_EXEC

            vaddr = elf_segment.header.p_vaddr

            if elf.header.e_type == "ET_EXEC" or load_addr_set:
                elf_type |= MAP_FIXED

            elif no_base and elf.header.e_type == "ET_DYN":
                load_addr = -vaddr

            map_addr = self.__elf_map__(open(interpreter), load_addr + vaddr, elf_segment, elf_prot, elf_type,
                                        total_size)
            total_size = 0

            if not load_addr_set and elf.header.e_type == "ET_DYN":
                load_addr = map_addr - PAGE_START(vaddr)
                load_addr_set = 1

            # k = load_addr + eppnt->p_vaddr + eppnt->p_filesz
            k = load_addr + elf_segment.header.p_vaddr + elf_segment.header.p_filesz

            if k > elf_bss:
                elf_bss = k

            # k = load_addr + eppnt->p_memsz + eppnt->p_vaddr;
            k = load_addr + elf_segment.header.p_memsz + elf_segment.header.p_vaddr

            if k > last_bss:
                last_bss = k

        if last_bss > elf_bss:
            elf_bss = PAGE_START(elf_bss + PAGE_SIZE - 1)
            self.__set_brk__(elf_bss, last_bss - elf_bss)

        return load_addr

    def __align_stack__(self, p):
        raise NotImplementedError()

    def __stack_push__(self, sp, value):
        raise NotImplementedError()

    def __stack_alloc__(self, sp, len_):
        raise NotImplementedError()

    def __vectors_user_mapping__(self):
        raise NotImplementedError()

    def __elf_plat_init__(self, load_addr):
        raise NotImplementedError()

    def __start_thread__(self, elf_entry, stack):
        raise NotImplementedError()

    def __dispatch_syscall__(self):
        raise NotImplementedError()

    def sys_fork(self):
        """
        """
        raise MissingSyscallException("fork")

    def sys_clone(self):
        """
        """
        raise MissingSyscallException("clone")

    def sys_setuid32(self):
        """
        """
        raise MissingSyscallException("setuid32")

    def sys_getuid32(self):
        """
        """
        raise MissingSyscallException("getuid32")

    def sys_getgid32(self):
        """
        """
        raise MissingSyscallException("getgid32")

    def sys_geteuid32(self):
        """
        """
        raise MissingSyscallException("geteuid32")

    def sys_getegid32(self):
        """
        """
        raise MissingSyscallException("getegid32")

    def sys_getresuid32(self):
        """
        """
        raise MissingSyscallException("getresuid32")

    def sys_getresgid32(self):
        """
        """
        raise MissingSyscallException("getresgid32")

    def sys_gettid(self):
        """
        """
        raise MissingSyscallException("gettid")

    def sys_getgroups32(self):
        """
        """
        raise MissingSyscallException("getgroups32")

    def sys_setsid(self):
        """
        """
        raise MissingSyscallException("setsid")

    def sys_setgid32(self):
        """
        """
        raise MissingSyscallException("setgid32")

    def sys_setreuid32(self):
        """
        """
        raise MissingSyscallException("setreuid32")

    def sys_setresuid32(self):
        """
        """
        raise MissingSyscallException("setresuid32")

    def sys_setresgid32(self):
        """
        """
        raise MissingSyscallException("setresgid32")

    def sys_setrlimit(self):
        """
        """
        raise MissingSyscallException("setrlimit")

    def sys_ugetrlimit(self):
        """
        """
        raise MissingSyscallException("ugetrlimit")

    def sys_getrusage(self):
        """
        """
        raise MissingSyscallException("getrusage")

    def sys_setgroups32(self):
        """
        """
        raise MissingSyscallException("setgroups32")

    def sys_setpgid(self):
        """
        """
        raise MissingSyscallException("setpgid")

    def sys_setregid32(self):
        """
        """
        raise MissingSyscallException("setregid32")

    def sys_chroot(self):
        """
        """
        raise MissingSyscallException("chroot")

    def sys_prctl(self):
        """
        """
        raise MissingSyscallException("prctl")

    def sys_capget(self):
        """
        """
        raise MissingSyscallException("capget")

    def sys_capset(self):
        """
        """
        raise MissingSyscallException("capset")

    def sys_pread64(self):
        """
        """
        raise MissingSyscallException("pread64")

    def sys_pwrite64(self):
        """
        """
        raise MissingSyscallException("pwrite64")

    def sys_lseek(self):
        """
        """
        raise MissingSyscallException("lseek")

    def sys_llseek(self):
        """
        """
        raise MissingSyscallException("_llseek")

    def sys_mmap2(self):
        """
        """
        raise MissingSyscallException("mmap2")

    def sys_mremap(self):
        """
        """
        raise MissingSyscallException("mremap")

    def sys_msync(self):
        """
        """
        raise MissingSyscallException("msync")

    def sys_mlock(self):
        """
        """
        raise MissingSyscallException("mlock")

    def sys_munlock(self):
        """
        """
        raise MissingSyscallException("munlock")

    def sys_readv(self, fd, iov, iovcnt):
        """
        readv, writev, preadv, pwritev - read or write data into multiple buffers
        """
        raise MissingSyscallException("readv")

    def sys_writev(self, fd, iov, iovcnt):
        """
        readv, writev, preadv, pwritev - read or write data into multiple buffers

        struct iovec {
            void  *iov_base;    /* Starting address */
            size_t iov_len;     /* Number of bytes to transfer */
        };
        """        
        total = 0
        for i in xrange(0, iovcnt):
            buf = self.cpu.get_dword(iov + (i * 8))
            size = self.cpu.get_dword((iov + (i * 8)) + 4)

            data = self.cpu.get_bytes(buf, size)
            
            # log.info("DEBUG: %.8x %d" % (buf, size))
            # log.info("DEBUG: %s" % (data))
            
            self.files[fd].write(data)
            total += size
        
        return total

    def sys_fcntl(self):
        """
        """
        raise MissingSyscallException("fcntl")

    def sys_flock(self):
        """
        """
        raise MissingSyscallException("flock")

    def sys_fchmod(self):
        """
        """
        raise MissingSyscallException("fchmod")

    def sys_dup(self):
        """
        """
        raise MissingSyscallException("dup")

    def sys_pipe(self):
        """
        """
        raise MissingSyscallException("pipe")

    def sys_dup2(self):
        """
        """
        raise MissingSyscallException("dup2")

    def sys_newselect(self):
        """
        """
        raise MissingSyscallException("newselect")

    def sys_ftruncate(self):
        """
        """
        raise MissingSyscallException("ftruncate")

    def sys_fsync(self):
        """
        """
        raise MissingSyscallException("fsync")

    def sys_fchown32(self):
        """
        """
        raise MissingSyscallException("fchown32")

    def sys_sync(self):
        """
        """
        raise MissingSyscallException("sync")

    def sys_fcntl64(self):
        """
        """
        raise MissingSyscallException("fcntl64")

    def sys_sendfile(self):
        """
        """
        raise MissingSyscallException("sendfile")

    def sys_link(self):
        """
        """
        raise MissingSyscallException("link")

    def sys_unlink(self):
        """
        """
        raise MissingSyscallException("unlink")

    def sys_chdir(self):
        """
        """
        raise MissingSyscallException("chdir")

    def sys_mknod(self):
        """
        """
        raise MissingSyscallException("mknod")

    def sys_chmod(self):
        """
        """
        raise MissingSyscallException("chmod")

    def sys_chown32(self):
        """
        """
        raise MissingSyscallException("chown32")

    def sys_lchown32(self):
        """
        """
        raise MissingSyscallException("lchown32")

    def sys_mount(self):
        """
        """
        raise MissingSyscallException("mount")

    def sys_umount2(self):
        """
        """
        raise MissingSyscallException("umount2")

    def sys_fstat64(self):
        """
        """
        raise MissingSyscallException("fstat64")

    def sys_stat64(self):
        """
        """
        raise MissingSyscallException("stat64")

    def sys_lstat64(self):
        """
        """
        raise MissingSyscallException("lstat64")

    def sys_mkdir(self):
        """
        """
        raise MissingSyscallException("mkdir")

    def sys_readlink(self):
        """
        """
        raise MissingSyscallException("readlink")

    def sys_rmdir(self):
        """
        """
        raise MissingSyscallException("rmdir")

    def sys_rename(self):
        """
        """
        raise MissingSyscallException("rename")

    def sys_getcwd(self):
        """
        """
        raise MissingSyscallException("getcwd")

    def sys_symlink(self):
        """
        """
        raise MissingSyscallException("symlink")

    def sys_fchdir(self):
        """
        """
        raise MissingSyscallException("fchdir")

    def sys_truncate(self):
        """
        """
        raise MissingSyscallException("truncate")

    def sys_pause(self):
        """
        """
        raise MissingSyscallException("pause")

    def sys_gettimeofday(self):
        """
        """
        raise MissingSyscallException("gettimeofday")

    def sys_settimeofday(self):
        """
        """
        raise MissingSyscallException("settimeofday")

    def sys_times(self):
        """
        """
        raise MissingSyscallException("times")

    def sys_nanosleep(self):
        """
        """
        raise MissingSyscallException("nanosleep")

    def sys_getitimer(self):
        """
        """
        raise MissingSyscallException("getitimer")

    def sys_setitimer(self):
        """
        """
        raise MissingSyscallException("setitimer")

    def sys_sigaction(self):
        """
        """
        raise MissingSyscallException("sigaction")

    def sys_sigprocmask(self):
        """
        """
        raise MissingSyscallException("sigprocmask")

    def sys_sigsuspend(self):
        """
        """
        raise MissingSyscallException("sigsuspend")

    def sys_rt_sigtimedwait(self):
        """
        """
        raise MissingSyscallException("rt_sigtimedwait")

    def sys_sigpending(self):
        """
        """
        raise MissingSyscallException("sigpending")

    def sys_sched_setscheduler(self):
        """
        """
        raise MissingSyscallException("sched_setscheduler")

    def sys_sched_getscheduler(self):
        """
        """
        raise MissingSyscallException("sched_getscheduler")

    def sys_sched_yield(self):
        """
        """
        raise MissingSyscallException("sched_yield")

    def sys_sched_setparam(self):
        """
        """
        raise MissingSyscallException("sched_setparam")

    def sys_sched_getparam(self):
        """
        """
        raise MissingSyscallException("sched_getparam")

    def sys_sched_get_priority_max(self):
        """
        """
        raise MissingSyscallException("sched_get_priority_max")

    def sys_sched_get_priority_min(self):
        """
        """
        raise MissingSyscallException("sched_get_priority_min")

    def sys_sched_rr_get_interval(self):
        """
        """
        raise MissingSyscallException("sched_rr_get_interval")

    def sys_wait4(self):
        """
        """
        raise MissingSyscallException("wait4")

    def sys_umask(self):
        """
        """
        raise MissingSyscallException("umask")

    def sys_reboot(self):
        """
        """
        raise MissingSyscallException("reboot")

    def sys_syslog(self):
        """
        """
        raise MissingSyscallException("syslog")

    def sys_init_module(self):
        """
        """
        raise MissingSyscallException("init_module")

    def sys_delete_module(self):
        """
        """
        raise MissingSyscallException("delete_module")

    def sys_poll(self):
        """
        """
        raise MissingSyscallException("poll")

    def sys_waitid(self):
        """
        """
        raise MissingSyscallException("waitid")

    def sys_vfork(self):
        """
        """
        raise MissingSyscallException("vfork")

    def sys_madvise(self):
        """
        """
        raise MissingSyscallException("madvise")

    def sys_mincore(self):
        """
        """
        raise MissingSyscallException("mincore")

    def sys_getdents64(self):
        """
        """
        raise MissingSyscallException("getdents64")

    def sys_fstatfs64(self):
        """
        """
        raise MissingSyscallException("fstatfs64")

    def sys_fstatat64(self):
        """
        """
        raise MissingSyscallException("fstatat64")

    def sys_mkdirat(self):
        """
        """
        raise MissingSyscallException("mkdirat")

    def sys_fchownat(self):
        """
        """
        raise MissingSyscallException("fchownat")

    def sys_fchmodat(self):
        """
        """
        raise MissingSyscallException("fchmodat")

    def sys_renameat(self):
        """
        """
        raise MissingSyscallException("renameat")

    def sys_unlinkat(self):
        """
        """
        raise MissingSyscallException("unlinkat")

    def sys_statfs64(self):
        """
        """
        raise MissingSyscallException("statfs64")

    def sys_clock_gettime(self):
        """
        """
        raise MissingSyscallException("clock_gettime")

    def sys_clock_settime(self):
        """
        """
        raise MissingSyscallException("clock_settime")

    def sys_clock_getres(self):
        """
        """
        raise MissingSyscallException("clock_getres")

    def sys_clock_nanosleep(self):
        """
        """
        raise MissingSyscallException("clock_nanosleep")

    def sys_timer_create(self):
        """
        """
        raise MissingSyscallException("timer_create")

    def sys_timer_settime(self):
        """
        """
        raise MissingSyscallException("timer_settime")

    def sys_timer_gettime(self):
        """
        """
        raise MissingSyscallException("timer_gettime")

    def sys_timer_getoverrun(self):
        """
        """
        raise MissingSyscallException("timer_getoverrun")

    def sys_timer_delete(self):
        """
        """
        raise MissingSyscallException("timer_delete")

    def sys_utimes(self):
        """
        """
        raise MissingSyscallException("utimes")

    def sys_socket(self):
        """
        """
        raise MissingSyscallException("socket")

    def sys_socketpair(self):
        """
        """
        raise MissingSyscallException("socketpair")

    def sys_bind(self):
        """
        """
        raise MissingSyscallException("bind")

    def sys_connect(self):
        """
        """
        raise MissingSyscallException("connect")

    def sys_listen(self):
        """
        """
        raise MissingSyscallException("listen")

    def sys_accept(self, sockfd, addr, addrlen):
        """
        """
        raise MissingSyscallException("accept")

    def sys_getsockname(self):
        """
        """
        raise MissingSyscallException("getsockname")

    def sys_getpeername(self):
        """
        """
        raise MissingSyscallException("getpeername")

    def sys_sendto(self):
        """
        """
        raise MissingSyscallException("sendto")

    def sys_recvfrom(self):
        """
        """
        raise MissingSyscallException("recvfrom")

    def sys_shutdown(self):
        """
        """
        raise MissingSyscallException("shutdown")

    def sys_setsockopt(self):
        """
        """
        raise MissingSyscallException("setsockopt")

    def sys_getsockopt(self):
        """
        """
        raise MissingSyscallException("getsockopt")

    def sys_sendmsg(self):
        """
        """
        raise MissingSyscallException("sendmsg")

    def sys_recvmsg(self):
        """
        """
        raise MissingSyscallException("recvmsg")

    def sys_epoll_create(self):
        """
        """
        raise MissingSyscallException("epoll_create")

    def sys_epoll_ctl(self):
        """
        """
        raise MissingSyscallException("epoll_ctl")

    def sys_epoll_wait(self):
        """
        """
        raise MissingSyscallException("epoll_wait")

    def sys_inotify_init(self):
        """
        """
        raise MissingSyscallException("inotify_init")

    def sys_inotify_add_watch(self):
        """
        """
        raise MissingSyscallException("inotify_add_watch")

    def sys_inotify_rm_watch(self):
        """
        """
        raise MissingSyscallException("inotify_rm_watch")

    def sys_ARM_set_tls(self):
        """
        """
        raise MissingSyscallException("ARM_set_tls")

    def sys_ARM_cacheflush(self):
        """
        """
        raise MissingSyscallException("ARM_cacheflush")

    def sys_getpid(self):
        """
        getpid, getppid - get process identification
        """
        return os.getpid()
    
    def sys_getppid(self):
        """
        getpid, getppid - get process identification
        """
        return os.getppid()
    
    def sys_getpgid(self):
        """
        setpgid, getpgid, setpgrp, getpgrp - set/get process group
        """
        return os.getpgid()    

    def sys_getpriority(self, which, who):
        """
        getpriority, setpriority - get/set program scheduling priority
        Ignored.
        """
        return 0

    def sys_setpriority(self, which, who, prio):
        """
        getpriority, setpriority - get/set program scheduling priority
        Ignored.
        """
        return 0

    def sys_ptrace(self, request, pid, addr, data):
        """
        ptrace - process trace
        Not implemented.
        """
        return -1

    def sys_acct(self, filename):
        """
        acct - switch process accounting on or off
        Not implemented, returns failure.
        """
        return -1

    def sys_uname(self, buf):
        """
        uname - get name and information about current kernel
        """
        uname = "Linux" + '\x00' * (65 - 5)
        uname += "localhost" + '\x00' * (65 - 9)
        uname += "3.9.2-GANOOO" + '\x00' * (65 - 12)
        uname += "#2 SMP Fri May 17 21:08:46 ART 2013" + '\x00' * (65 - 35)
        uname += "ARM_??" + '\x00' * (65 - 6)
        uname += "(none)" + '\x00' * (65 - 6)
        self.cpu.set_bytes(buf, uname)
        return 0

    def sys_access(self, pathname, mode):
        """
        access - check real user's permissions for a file
        """
        return 0 if os.access(self.cpu.read_c_string(pathname), mode) else -1
        
    def sys_arch_prctl(self, code, addr):
        """
        arch_prctl - set architecture-specific thread state
        """
        raise MissingSyscallException("Implement this syscall only in x86-64 bits")
        
    def sys_brk(self, addr):
        """
        brk, sbrk - change data segment size
        """
        if addr != 0:
            size = addr - self.elf_brk
            self.cpu.memset(self.elf_brk, 0, size)
            self.elf_brk += size

        return self.elf_brk
        
    def sys_close(self, fd):
        """
        close - close a file descriptor
        """
        self.files[fd].close()
        self.files[fd] = None
        return 0
            
    def sys_execve(self, filename, argv, envp):
        """
        execve - execute program
        """
        raise MissingSyscallException()
        
    def sys_exit_group(self, status):
        """
        exit_group - exit all threads in a process
        """
        raise EmulationExited("Process exited with status = 0x%.8x" % status)

    def sys_exit(self, status):
        """
        _exit, _Exit - terminate the calling process
        """
        raise EmulationExited("Process exited with status = 0x%.8x" % status)
        
    def sys_fstat(self, fd, buf):
        """
        stat, fstat, lstat - get file status
        """
        raise MissingSyscallException()
        
    def sys_futex(self, uaddr, op, val, timeout, uaddr2, val3):
        """
        futex - fast user-space locking
        """
        raise MissingSyscallException()
        
    def sys_getdents(self, fd, dirp, count):
        """
        getdents - get directory entries
        """
        raise MissingSyscallException()
        
    def sys_getrlimit(self, resourse, rlim):
        """
        getrlimit, setrlimit, prlimit - get/set resource limits
        """
        raise MissingSyscallException()
        
    def sys_ioctl(self, fd, request):
        """
        ioctl - control device
        """
        return self.files[fd].ioctl(request)
                
    def sys_mprotect(self, addr, len_, prot):
        """
        mprotect - set protection on a region of memory
        """
        raise MissingSyscallException()
        
    def sys_munmap(self, addr, length):
        """
        mmap, munmap - map or unmap files or devices into memory
        """
        raise MissingSyscallException()
        
    def sys_openat(self, dirfd, pathname, flags, mode):
        """
        openat - open a file relative to a directory file descriptor
        """
        raise MissingSyscallException()
        
    def sys_open(self, pathname, flags, mode):
        """
        open, creat - open and possibly create a file or device
        
        open() and creat() return the new file descriptor, or -1 if an error occurred.        
        """        
        path = self.cpu.read_c_string(pathname)
        if path[0] == os.path.sep:
            path = path[1:]
            
        path = os.path.join(self.root_dir, path)
                
        try:
            f = File(path, flags)
        
        except IOError:
            log.info("sys_open: Could not open %s" % path)
            return -1
        
        if None in self.files:
            fd = self.files.index(None)
            self.files[fd] = f
            
        else:
            self.files.append(f)
            fd = len(self.files) - 1

        return fd
        
    def sys_read(self, fd, buf, count):
        """
        read - read from a file descriptor
        """
        data = self.files[fd].read(count)
        self.cpu.set_bytes(buf, data)
        return len(data)
        
    def sys_rt_sigaction(self, signum, act, oldact):
        """
        sigaction - examine and change a signal action
        """
        raise MissingSyscallException()
        
    def sys_rt_sigprocmask(self, how, set_, oldset):
        """
        sigprocmask - examine and change blocked signals
        """
        raise MissingSyscallException()
        
    def sys_set_robust_list(self, head, len_):
        """
        get_robust_list, set_robust_list - get/set list of robust futexes
        """
        raise MissingSyscallException()
        
    def sys_set_tid_address(self, tidptr):
        """
        set_tid_address - set pointer to thread ID
        """
        raise MissingSyscallException()
        
    def sys_statfs(self, path, buf):
        """
        statfs, fstatfs - get file system statistics
        """
        raise MissingSyscallException()
        
    def sys_write(self, fd, buf, count):
        """
        write - write to a file descriptor
        """
        buf = self.cpu.get_bytes(buf, count)
        self.files[fd].write(buf)
        return count

    def sys_getuid(self, cpu):
        """
        getuid, geteuid - get user identity
        """
        return 1000

    def sys_getgid(self, cpu):
        """
        getgid, getegid - get group identity
        """
        return 1000

    def sys_geteuid(self, cpu):
        """
        getuid, geteuid - get user identity
        """
        return 1000

    def sys_getegid(self, cpu):
        """
        getgid, getegid - get group identity
        """
        return 1000
        
    def sys_mmap(self, addr, length, prot, flags, fd, offset):
        """
        @addr: starting address for the new mapping.
        @length: length of the mapping.
        @prot: desired memory protections.
        @flags: determines whether updates to the mapping are visible to other
                processes mapping the same region, and whether updates are carried
                through to the underlying file
        @fd: file object with the contents for the mapping.
        @offset: offset inside the fd.
        TODO: Implement.
        """
        task = self.get_current_task()

        # Get the next free address aligned to the page boundary.
        if not addr:
            # This could return None, so default to a somewhat sane address.
            tmp_addr = GetLastValidAddress(task.memory)
            if not tmp_addr:
                tmp_addr = 0x00400000

            addr = PAGE_ALIGN(tmp_addr)

        if fd:
            log.debug("sys_mmap: addr = %.8x | size = %.8x | prot = %s | flags = %s | fd = %.8x | offset = %.8x" % \
                     (addr, length, PROT_TO_DESC(prot), MAP_TO_DESC(flags), fd.fileno(), offset))

            # Read from the file.
            old_offset = fd.tell()
            fd.seek(offset)
            bytes_ = fd.read(length)

            # Reset the descriptor.
            fd.seek(old_offset)

            assert len(bytes_) == length, "Error reading bytes from fd"

            # Set the bytes in the memory map.
            task.memory.set_bytes(addr, bytes_)

        else:
            log.debug("sys_mmap: addr = %.8x | size = %.8x | prot = %s | flags = %s | fd = %.8x | offset = %.8x" % \
                     (addr, length, PROT_TO_DESC(prot), MAP_TO_DESC(flags), 0, offset))

            # Just set the memory range to 0x00
            task.memory.memset(addr, 0x00, length)

        return addr


    def execute(self, argv, envp):
        """
        Load the binary in memory and then call the interpreter
        to resolve what is needed. The interpreter will be emulated so
        we do not need to code anything.

        Implemented following binfmt_elf.c from the linux kernel.
        """
        interpreter = None
        binary = argv[0]

        log.info("Executing binary %s" % binary)
        main_binary = binary

        # Read the elf file.
        elf = ELFFile(file(binary))
        assert elf.header.e_type in ['ET_EXEC'], "We can only load binaries or shared objects."

        interpreter_name = "no_interpreter"

        # Find the ELF interpreter.
        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != 'PT_INTERP':
                continue

            # Get the interpretar name, make the path relative to CWD.
            interpreter_name = elf_segment.data()[:-1]
            if not os.path.exists(interpreter_name):
                interpreter_name = os.path.basename(interpreter_name)
                interpreter_name = os.path.join(os.getcwd(), "testfiles", interpreter_name)

                if not os.path.exists(interpreter_name):
                    raise RuntimeError("Could not find interpreter %s" % interpreter_name)

            # Read the interpreter's elf.
            interpreter = ELFFile(file(interpreter_name))

            break

        # Check that the interpreter matches the binary.
        if interpreter is not None:
            assert interpreter.get_machine_arch() == elf.get_machine_arch()
            assert interpreter.header.e_type in ['ET_DYN', 'ET_EXEC']

            log.info("Found interpreter %s" % interpreter_name)

        # Check if the binary espeficies whether it's stack is executable or not.
        executable_stack = False
        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != 'PT_GNU_STACK':
                continue

            if elf_segment.header.p_flags & 0x01:
                executable_stack = True

            else:
                executable_stack = False

            break

        elf_bss = 0
        start_code = 0xffffffff
        end_code = 0
        start_data = 0
        end_data = 0
        elf_brk = 0
        load_bias = 0
        elf_prot = 0
        load_addr = 0
        load_addr_set = 0
        interp_load_addr = 0

        # Load all the loadable segments.
        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type not in ['PT_LOAD']:
                continue

            if elf_brk > elf_bss:
                raise Exception("elf_brk > elf_bss")

            # Decode protection.
            if elf_segment.header.p_flags & PF_R:
                elf_prot |= PROT_READ

            if elf_segment.header.p_flags & PF_W:
                elf_prot |= PROT_WRITE

            if elf_segment.header.p_flags & PF_X:
                elf_prot |= PROT_EXEC

            # mmap flags
            elf_flags = MAP_PRIVATE | MAP_EXECUTABLE | MAP_FIXED

            vaddr = elf_segment.header.p_vaddr

            # Map the segment.
            error = self.__elf_map__(open(main_binary), load_bias + vaddr, elf_segment, elf_prot, elf_flags, 0)

            if not load_addr_set:
                load_addr_set = True

                load_addr = elf_segment.header.p_vaddr - elf_segment.header.p_offset
                if elf.header.e_type == "ET_DYN":
                    load_bias += error - PAGE_START(load_bias + vaddr)
                    load_addr += load_bias
                    reloc_func_desc = load_bias

            k = elf_segment.header.p_vaddr
            if k < start_code:
                start_code = k

            if start_data < k:
                start_data = k

            k = elf_segment.header.p_vaddr + elf_segment.header.p_filesz

            if k > elf_bss:
                elf_bss = k

            if (elf_segment.header.p_flags & PF_X) and end_code < k:
                end_code = k

            if end_data < k:
                end_data = k

            k = elf_segment.header.p_vaddr + elf_segment.header.p_memsz
            if k > elf_brk:
                elf_brk = k


        # Now we have all the segments loaded.
        elf.header.e_entry += load_bias
        elf_bss += load_bias
        elf_brk += load_bias
        start_code += load_bias
        end_code += load_bias
        start_data += load_bias
        end_data += load_bias

        log.debug("ELF elf_bss    : %.8x" % elf_bss)
        log.debug("ELF elf_brk    : %.8x" % elf_brk)
        log.debug("ELF start_code : %.8x" % start_code)
        log.debug("ELF end_code   : %.8x" % end_code)
        log.debug("ELF start_data : %.8x" % start_data)
        log.debug("ELF end_data   : %.8x" % end_data)

        self.elf_brk = PAGE_ALIGN(elf_brk)

        self.__set_brk__(elf_bss, elf_brk)

        if interpreter:
            elf_entry = self.__load_elf_interp__(interpreter, interpreter_name)
            interp_load_addr = elf_entry
            elf_entry += interpreter.header.e_entry
            reloc_func_desc = interp_load_addr

            log.info("Loaded ELF interpreter, entry point @ %.8x" % elf_entry)

        else:
            elf_entry = elf.header.e_entry

            log.info("Loaded ELF, entry point @ %.8x" % elf_entry)

        # This is ARM specific.
        self.__vectors_user_mapping__()

        # Here we define our stack.
        stack_top = 0xc0000000
        stack_size = 0x21000
        stack_base = stack_top - stack_size

        # Current stack pointer value.
        stack = stack_top

        # Get the task descriptor.
        task = self.get_current_task()

        # Initialize the stack to zeros.
        task.memory.memset(stack_base, 0x00, stack_size)

        # Make room for the 'end marker'
        stack = self.__stack_push__(stack, 0)

        # Save a pointer to each of the stack addresses of the env and arg variables.
        argvlst = []
        envplst = []

        # Place each of the environment variables.
        for env_var in envp:
            stack, env_address = self.__stack_alloc__(stack, len(env_var) + 1)
            task.memory.set_bytes(env_address, env_var + '\x00')
            envplst.append(env_address)

        # Place each of the arguments.
        for arg_var in argv:
            stack, arg_address = self.__stack_alloc__(stack, len(arg_var) + 1)
            task.memory.set_bytes(arg_address, arg_var + '\x00')
            argvlst.append(arg_address)

        stack, platform_addr = self.__stack_alloc__(stack, 4)
        task.memory.set_bytes(arg_address, "v7l\x00")
        
        # Align the stack since the strings may not be aligned.
        stack = ((stack - 4) / 4) * 4

        # Mark the end of the vector.
        stack = self.__stack_push__(stack, 0x00000000)
        stack = self.__stack_push__(stack, AT_NULL)

        # String identifying CPU for optimizations.
        stack = self.__stack_push__(stack, platform_addr)
        stack = self.__stack_push__(stack, AT_PLATFORM)  # f

        # Filename of program.
        stack = self.__stack_push__(stack, argvlst[0])
        stack = self.__stack_push__(stack, AT_EXECFN)  # 1f

        # Address of 16 random bytes. Secure crypto right here y0.
        stack = self.__stack_push__(stack, stack)
        stack = self.__stack_push__(stack, AT_RANDOM)  # 19

        # Secure mode boolean.
        stack = self.__stack_push__(stack, 0x00000000)
        stack = self.__stack_push__(stack, AT_SECURE)  # 17

        # Effective gid.
        stack = self.__stack_push__(stack, 1000)
        stack = self.__stack_push__(stack, AT_EGID)  # e

        # Real gid.
        stack = self.__stack_push__(stack, 1000)
        stack = self.__stack_push__(stack, AT_GID)  # d

        # Effective uid.
        stack = self.__stack_push__(stack, 1000)
        stack = self.__stack_push__(stack, AT_EUID)  # c

        # Real uid.
        stack = self.__stack_push__(stack, 1000)
        stack = self.__stack_push__(stack, AT_UID)  # b

        # Entry point of program.
        stack = self.__stack_push__(stack, elf.header.e_entry)
        stack = self.__stack_push__(stack, AT_ENTRY)

        # Flags.
        stack = self.__stack_push__(stack, 0x00000000)
        stack = self.__stack_push__(stack, AT_FLAGS)

        # Base address of interpreter.
        stack = self.__stack_push__(stack, interp_load_addr)
        stack = self.__stack_push__(stack, AT_BASE)        

        # Number of program headers.
        stack = self.__stack_push__(stack, elf.header.e_phnum)
        stack = self.__stack_push__(stack, AT_PHNUM)

        # Size of program header entry.
        stack = self.__stack_push__(stack, elf.header.e_phentsize)
        stack = self.__stack_push__(stack, AT_PHENT)

        # Program headers for program.
        stack = self.__stack_push__(stack, load_addr + elf.header.e_phoff)
        stack = self.__stack_push__(stack, AT_PHDR)
                
        # Frequency at which times() increments.
        stack = self.__stack_push__(stack, 0x00000064)
        stack = self.__stack_push__(stack, AT_CLKTCK)

        # System page size.
        stack = self.__stack_push__(stack, 0x00001000)
        stack = self.__stack_push__(stack, AT_PAGESZ)

        # Hardware capabilities found on QEMU for ARM.
        stack = self.__stack_push__(stack, 0x0000b0d7)
        stack = self.__stack_push__(stack, AT_HWCAP)

        # NULL envp
        stack = self.__stack_push__(stack, 0)

        # Fill 'char *envp[]' array.
        for envp_addr in reversed(envplst):
            stack = self.__stack_push__(stack, envp_addr)

        # NULL argv
        stack = self.__stack_push__(stack, 0)

        # Fill 'char *argv[]' array.
        for argv_addr in reversed(argvlst):
            stack = self.__stack_push__(stack, argv_addr)

        # Set the value of 'int argc'
        stack = self.__stack_push__(stack, len(argvlst))

        # log.info("Stack Dump:")
        # for addr, value in MemoryMapIterator(task.memory, start_addr=stack, end_addr=stack_top, step_size=4):
        #     log.info("\t[%.8x] = %.8x" % (addr, task.memory.get_dword(addr)))
        # 
        # for addr in xrange(stack, stack_top - 4 - 4, 4*4):
        #     a1 = task.memory.get_dword(addr + 4 * 0)
        #     a2 = task.memory.get_dword(addr + 4 * 1)
        #     a3 = task.memory.get_dword(addr + 4 * 2)
        #     a4 = task.memory.get_dword(addr + 4 * 3)
        #     print "0x%.8x: 0x%.8x  0x%.8x  0x%.8x  0x%.8x" % (addr, a1, a2, a3, a4)

        # Setup special registers following per-architecture ABI.
        self.__elf_plat_init__(reloc_func_desc)

        self.__start_thread__(elf_entry, stack)

        # Let the CPU consume instructions and execute.
        self.cpu.run()


SyscallInfo = namedtuple('SyscallInfo', ['name', 'number', 'nargs', 'format_string', 'handler'])

class ARMLinuxOS(LinuxOS):
    def __init__(self, settings):
        """
        Emulate Linux running on an ARM processor.
        """
        memory = ConcreteMemoryMap()
        cpu = ARMEmulator(memory, settings, self)
        self.stack_grows_down = True
        self.settings = settings
        self.root_dir = settings["root-dir"]
        
        super(ARMLinuxOS, self).__init__(cpu, memory)

        # Build the table that maps a syscall number to its descriptor with useful information
        # for its own handling.
        self.syscall_table = {}
        self.syscall_table[NR_exit] = SyscallInfo("exit", NR_exit, 1, "%d", self.sys_exit)
        self.syscall_table[NR_fork] = SyscallInfo("fork", NR_fork, 0, "", self.sys_fork)
        self.syscall_table[NR_clone] = SyscallInfo("clone", NR_clone, 4, "%p, %p, %d, %p", self.sys_clone)
        self.syscall_table[NR_execve] = SyscallInfo("execve", NR_execve, 3, "%p, %p, %p", self.sys_execve)
        self.syscall_table[NR_setuid32] = SyscallInfo("setuid32", NR_setuid32, 1, "%d", self.sys_setuid32)
        self.syscall_table[NR_getuid32] = SyscallInfo("getuid32", NR_getuid32, 0, "", self.sys_getuid32)
        self.syscall_table[NR_getgid32] = SyscallInfo("getgid32", NR_getgid32, 0, "", self.sys_getgid32)
        self.syscall_table[NR_geteuid32] = SyscallInfo("geteuid32", NR_geteuid32, 0, "", self.sys_geteuid32)
        self.syscall_table[NR_getegid32] = SyscallInfo("getegid32", NR_getegid32, 0, "", self.sys_getegid32)
        self.syscall_table[NR_getresuid32] = SyscallInfo("getresuid32", NR_getresuid32, 3, "%p, %p, %p", self.sys_getresuid32)
        self.syscall_table[NR_getresgid32] = SyscallInfo("getresgid32", NR_getresgid32, 3, "%p, %p, %p", self.sys_getresgid32)
        self.syscall_table[NR_gettid] = SyscallInfo("gettid", NR_gettid, 0, "", self.sys_gettid)
        self.syscall_table[NR_getgroups32] = SyscallInfo("getgroups32", NR_getgroups32, 2, "%d, %p", self.sys_getgroups32)
        self.syscall_table[NR_getpgid] = SyscallInfo("getpgid", NR_getpgid, 1, "%d", self.sys_getpgid)
        self.syscall_table[NR_getppid] = SyscallInfo("getppid", NR_getppid, 0, "", self.sys_getppid)
        self.syscall_table[NR_setsid] = SyscallInfo("setsid", NR_setsid, 0, "", self.sys_setsid)
        self.syscall_table[NR_setgid32] = SyscallInfo("setgid32", NR_setgid32, 1, "%d", self.sys_setgid32)
        self.syscall_table[NR_setreuid32] = SyscallInfo("setreuid32", NR_setreuid32, 2, "%d, %d", self.sys_setreuid32)
        self.syscall_table[NR_setresuid32] = SyscallInfo("setresuid32", NR_setresuid32, 3, "%d, %d, %d", self.sys_setresuid32)
        self.syscall_table[NR_setresgid32] = SyscallInfo("setresgid32", NR_setresgid32, 3, "%d, %d, %d", self.sys_setresgid32)
        self.syscall_table[NR_brk] = SyscallInfo("brk", NR_brk, 1, "%p", self.sys_brk)
        self.syscall_table[NR_ptrace] = SyscallInfo("ptrace", NR_ptrace, 4, "%d, %d, %p, %p", self.sys_ptrace)
        self.syscall_table[NR_getpriority] = SyscallInfo("getpriority", NR_getpriority, 2, "%d, %d", self.sys_getpriority)
        self.syscall_table[NR_setpriority] = SyscallInfo("setpriority", NR_setpriority, 3, "%d, %d, %d", self.sys_setpriority)        
        self.syscall_table[NR_setrlimit] = SyscallInfo("setrlimit", NR_setrlimit, 2, "%d, %p", self.sys_setrlimit)
        self.syscall_table[NR_ugetrlimit] = SyscallInfo("ugetrlimit", NR_ugetrlimit, 2, "%d, %p", self.sys_ugetrlimit)
        self.syscall_table[NR_getrusage] = SyscallInfo("getrusage", NR_getrusage, 2, "%d, %p", self.sys_getrusage)
        self.syscall_table[NR_setgroups32] = SyscallInfo("setgroups32", NR_setgroups32, 2, "%d, %p", self.sys_setgroups32)
        self.syscall_table[NR_setpgid] = SyscallInfo("setpgid", NR_setpgid, 2, "%d, %d", self.sys_setpgid)
        self.syscall_table[NR_setregid32] = SyscallInfo("setregid32", NR_setregid32, 2, "%d, %d", self.sys_setregid32)
        self.syscall_table[NR_chroot] = SyscallInfo("chroot", NR_chroot, 1, "%p", self.sys_chroot)
        self.syscall_table[NR_prctl] = SyscallInfo("prctl", NR_prctl, 5, "%d, %d, %d, %d, %d", self.sys_prctl)
        self.syscall_table[NR_capget] = SyscallInfo("capget", NR_capget, 2, "%d, %d", self.sys_capget)
        self.syscall_table[NR_capset] = SyscallInfo("capset", NR_capset, 2, "%d, %d", self.sys_capset)
        self.syscall_table[NR_acct] = SyscallInfo("acct", NR_acct, 1, "%p", self.sys_acct)
        self.syscall_table[NR_read] = SyscallInfo("read", NR_read, 3, "%d, %p, %d", self.sys_read)
        self.syscall_table[NR_write] = SyscallInfo("write", NR_write, 3, "%d, %p, %d", self.sys_write)
        self.syscall_table[NR_pread64] = SyscallInfo("pread64", NR_pread64, 4, "%d, %p, %d, %d", self.sys_pread64)
        self.syscall_table[NR_pwrite64] = SyscallInfo("pwrite64", NR_pwrite64, 4, "%d, %p, %d, %d", self.sys_pwrite64)
        self.syscall_table[NR_open] = SyscallInfo("open", NR_open, 3, "%p, %d, %d", self.sys_open)
        self.syscall_table[NR_close] = SyscallInfo("close", NR_close, 1, "%d", self.sys_close)
        self.syscall_table[NR_lseek] = SyscallInfo("lseek", NR_lseek, 3, "%d, %d, %d", self.sys_lseek)
        self.syscall_table[NRllseek] = SyscallInfo("llseek", NRllseek, 5, "%d, %d, %d, %p, %d", self.sys_llseek)
        self.syscall_table[NR_getpid] = SyscallInfo("getpid", NR_getpid, 0, "", self.sys_getpid)
        self.syscall_table[NR_mmap2] = SyscallInfo("mmap2", NR_mmap2, 6, "%p, %d, %d, %d, %d, %d", self.sys_mmap2)
        self.syscall_table[NR_munmap] = SyscallInfo("munmap", NR_munmap, 2, "%p, %d", self.sys_munmap)
        self.syscall_table[NR_mremap] = SyscallInfo("mremap", NR_mremap, 4, "%p, %d, %d, %d", self.sys_mremap)
        self.syscall_table[NR_msync] = SyscallInfo("msync", NR_msync, 3, "%p, %d, %d", self.sys_msync)
        self.syscall_table[NR_mprotect] = SyscallInfo("mprotect", NR_mprotect, 3, "%p, %d, %d", self.sys_mprotect)
        self.syscall_table[NR_mlock] = SyscallInfo("mlock", NR_mlock, 2, "%p, %d", self.sys_mlock)
        self.syscall_table[NR_munlock] = SyscallInfo("munlock", NR_munlock, 2, "%p, %d", self.sys_munlock)
        self.syscall_table[NR_ioctl] = SyscallInfo("ioctl", NR_ioctl, 2, "%d, %d", self.sys_ioctl)
        self.syscall_table[NR_readv] = SyscallInfo("readv", NR_readv, 3, "%d, %p, %d", self.sys_readv)
        self.syscall_table[NR_writev] = SyscallInfo("writev", NR_writev, 3, "%d, %p, %d", self.sys_writev)
        self.syscall_table[NR_fcntl] = SyscallInfo("fcntl", NR_fcntl, 2, "%d, %d", self.sys_fcntl)
        self.syscall_table[NR_flock] = SyscallInfo("flock", NR_flock, 2, "%d, %d", self.sys_flock)
        self.syscall_table[NR_fchmod] = SyscallInfo("fchmod", NR_fchmod, 2, "%d, %d", self.sys_fchmod)
        self.syscall_table[NR_dup] = SyscallInfo("dup", NR_dup, 1, "%d", self.sys_dup)
        self.syscall_table[NR_pipe] = SyscallInfo("pipe", NR_pipe, 1, "%p", self.sys_pipe)
        self.syscall_table[NR_dup2] = SyscallInfo("dup2", NR_dup2, 2, "%d, %d", self.sys_dup2)
        self.syscall_table[NRnewselect] = SyscallInfo("newselect", NRnewselect, 0, "", self.sys_newselect)  # TODO: What do? No MAN
        self.syscall_table[NR_ftruncate] = SyscallInfo("ftruncate", NR_ftruncate, 2, "%p, %d", self.sys_ftruncate)
        self.syscall_table[NR_fsync] = SyscallInfo("fsync", NR_fsync, 1, "%d", self.sys_fsync)
        self.syscall_table[NR_fchown32] = SyscallInfo("fchown32", NR_fchown32, 3, "%d, %d, %d", self.sys_fchown32)
        self.syscall_table[NR_sync] = SyscallInfo("sync", NR_sync, 0, "", self.sys_sync)
        self.syscall_table[NR_fcntl64] = SyscallInfo("fcntl64", NR_fcntl64, 2, "%d, %d", self.sys_fcntl64)
        self.syscall_table[NR_sendfile] = SyscallInfo("sendfile", NR_sendfile, 4, "%d, %d, %p, %d", self.sys_sendfile)
        self.syscall_table[NR_link] = SyscallInfo("link", NR_link, 2, "%p, %p", self.sys_link)
        self.syscall_table[NR_unlink] = SyscallInfo("unlink", NR_unlink, 1, "%p", self.sys_unlink)
        self.syscall_table[NR_chdir] = SyscallInfo("chdir", NR_chdir, 1, "%p", self.sys_chdir)
        self.syscall_table[NR_mknod] = SyscallInfo("mknod", NR_mknod, 3, "%p, %d, %d", self.sys_mknod)
        self.syscall_table[NR_chmod] = SyscallInfo("chmod", NR_chmod, 2, "%p, %d", self.sys_chmod)
        self.syscall_table[NR_chown32] = SyscallInfo("chown32", NR_chown32, 3, "%p, %d, %d", self.sys_chown32)
        self.syscall_table[NR_lchown32] = SyscallInfo("lchown32", NR_lchown32, 3, "%p, %d, %d", self.sys_lchown32)
        self.syscall_table[NR_mount] = SyscallInfo("mount", NR_mount, 5, "%p, %p, %p, %d, %p", self.sys_mount)
        self.syscall_table[NR_umount2] = SyscallInfo("umount2", NR_umount2, 2, "%p, %d", self.sys_umount2)
        self.syscall_table[NR_fstat64] = SyscallInfo("fstat64", NR_fstat64, 2, "%d, %p", self.sys_fstat64)
        self.syscall_table[NR_stat64] = SyscallInfo("stat64", NR_stat64, 2, "%p, %p", self.sys_stat64)
        self.syscall_table[NR_lstat64] = SyscallInfo("lstat64", NR_lstat64, 2, "%p, %p", self.sys_lstat64)
        self.syscall_table[NR_mkdir] = SyscallInfo("mkdir", NR_mkdir, 2, "%p, %d", self.sys_mkdir)
        self.syscall_table[NR_readlink] = SyscallInfo("readlink", NR_readlink, 3, "%p, %p, %d", self.sys_readlink)
        self.syscall_table[NR_rmdir] = SyscallInfo("rmdir", NR_rmdir, 1, "%p", self.sys_rmdir)
        self.syscall_table[NR_rename] = SyscallInfo("rename", NR_rename, 2, "%p, %p", self.sys_rename)
        self.syscall_table[NR_getcwd] = SyscallInfo("getcwd", NR_getcwd, 2, "%p, %d", self.sys_getcwd)
        self.syscall_table[NR_access] = SyscallInfo("access", NR_access, 2, "%p, %d", self.sys_access)
        self.syscall_table[NR_symlink] = SyscallInfo("symlink", NR_symlink, 2, "%p, %p", self.sys_symlink)
        self.syscall_table[NR_fchdir] = SyscallInfo("fchdir", NR_fchdir, 1, "%d", self.sys_fchdir)
        self.syscall_table[NR_truncate] = SyscallInfo("truncate", NR_truncate, 2, "%p, %d", self.sys_truncate)
        self.syscall_table[NR_pause] = SyscallInfo("pause", NR_pause, 0, "", self.sys_pause)
        self.syscall_table[NR_gettimeofday] = SyscallInfo("gettimeofday", NR_gettimeofday, 2, "%p, %p", self.sys_gettimeofday)
        self.syscall_table[NR_settimeofday] = SyscallInfo("settimeofday", NR_settimeofday, 2, "%p, %p", self.sys_settimeofday)
        self.syscall_table[NR_times] = SyscallInfo("times", NR_times, 1, "%p", self.sys_times)
        self.syscall_table[NR_nanosleep] = SyscallInfo("nanosleep", NR_nanosleep, 2, "%p, %p", self.sys_nanosleep)
        self.syscall_table[NR_getitimer] = SyscallInfo("getitimer", NR_getitimer, 2, "%d, %p", self.sys_getitimer)
        self.syscall_table[NR_setitimer] = SyscallInfo("setitimer", NR_setitimer, 3, "%d, %p, %p", self.sys_setitimer)
        self.syscall_table[NR_sigaction] = SyscallInfo("sigaction", NR_sigaction, 3, "%d, %p, %p", self.sys_sigaction)
        self.syscall_table[NR_sigprocmask] = SyscallInfo("sigprocmask", NR_sigprocmask, 3, "%d, %p, %p", self.sys_sigprocmask)
        self.syscall_table[NR_sigsuspend] = SyscallInfo("sigsuspend", NR_sigsuspend, 1, "%p", self.sys_sigsuspend)
        self.syscall_table[NR_rt_sigaction] = SyscallInfo("rt_sigaction", NR_rt_sigaction, 3, "%d, %p, %p", self.sys_rt_sigaction)
        self.syscall_table[NR_rt_sigprocmask] = SyscallInfo("rt_sigprocmask", NR_rt_sigprocmask, 3, "%d, %p, %p", self.sys_rt_sigprocmask)
        self.syscall_table[NR_rt_sigtimedwait] = SyscallInfo("rt_sigtimedwait", NR_rt_sigtimedwait, 3, "%p, %p, %p", self.sys_rt_sigtimedwait)
        self.syscall_table[NR_sigpending] = SyscallInfo("sigpending", NR_sigpending, 1, "%p", self.sys_sigpending)
        self.syscall_table[NR_sched_setscheduler] = SyscallInfo("sched_setscheduler", NR_sched_setscheduler, 3, "%d, %d, %p", self.sys_sched_setscheduler)
        self.syscall_table[NR_sched_getscheduler] = SyscallInfo("sched_getscheduler", NR_sched_getscheduler, 1, "%d", self.sys_sched_getscheduler)
        self.syscall_table[NR_sched_yield] = SyscallInfo("sched_yield", NR_sched_yield, 0, "", self.sys_sched_yield)
        self.syscall_table[NR_sched_setparam] = SyscallInfo("sched_setparam", NR_sched_setparam, 2, "%d, %p", self.sys_sched_setparam)
        self.syscall_table[NR_sched_getparam] = SyscallInfo("sched_getparam", NR_sched_getparam, 2, "%d, %p", self.sys_sched_getparam)
        self.syscall_table[NR_sched_get_priority_max] = SyscallInfo("sched_get_priority_max", NR_sched_get_priority_max, 1, "%d", self.sys_sched_get_priority_max)
        self.syscall_table[NR_sched_get_priority_min] = SyscallInfo("sched_get_priority_min", NR_sched_get_priority_min, 1, "%d", self.sys_sched_get_priority_min)
        self.syscall_table[NR_sched_rr_get_interval] = SyscallInfo("sched_rr_get_interval", NR_sched_rr_get_interval, 2, "%d, %p", self.sys_sched_rr_get_interval)
        self.syscall_table[NR_uname] = SyscallInfo("uname", NR_uname, 1, "%p", self.sys_uname)
        self.syscall_table[NR_wait4] = SyscallInfo("wait4", NR_wait4, 4, "%d, %p, %d, %p", self.sys_wait4)
        self.syscall_table[NR_umask] = SyscallInfo("umask", NR_umask, 1, "%d", self.sys_umask)
        self.syscall_table[NR_reboot] = SyscallInfo("reboot", NR_reboot, 1, "%d", self.sys_reboot)
        self.syscall_table[NR_syslog] = SyscallInfo("syslog", NR_syslog, 3, "%d, %p, %d", self.sys_syslog)
        self.syscall_table[NR_init_module] = SyscallInfo("init_module", NR_init_module, 2, "%p, %p", self.sys_init_module)
        self.syscall_table[NR_delete_module] = SyscallInfo("delete_module", NR_delete_module, 1, "%p", self.sys_delete_module)
        self.syscall_table[NR_futex] = SyscallInfo("futex", NR_futex, 6, "%p, %d, %d, %p, %p, %d", self.sys_futex)
        self.syscall_table[NR_poll] = SyscallInfo("poll", NR_poll, 3, "%p, %d, %d", self.sys_poll)
        self.syscall_table[NR_exit_group] = SyscallInfo("exit_group", NR_exit_group, 1, "%d", self.sys_exit_group)
        self.syscall_table[NR_waitid] = SyscallInfo("waitid", NR_waitid, 4, "%d, %d, %p, %d", self.sys_waitid)
        self.syscall_table[NR_vfork] = SyscallInfo("vfork", NR_vfork, 0, "", self.sys_vfork)
        self.syscall_table[NR_openat] = SyscallInfo("openat", NR_openat, 4, "%d, %p, %d, %d", self.sys_openat)
        self.syscall_table[NR_madvise] = SyscallInfo("madvise", NR_madvise, 3, "%p, %d, %d", self.sys_madvise)
        self.syscall_table[NR_mincore] = SyscallInfo("mincore", NR_mincore, 4, "%p, %d, %p", self.sys_mincore)
        self.syscall_table[NR_getdents64] = SyscallInfo("getdents64", NR_getdents64, 3, "%d, %p, %d", self.sys_getdents64)
        self.syscall_table[NR_fstatfs64] = SyscallInfo("fstatfs64", NR_fstatfs64, 2, "%d, %p", self.sys_fstatfs64)
        self.syscall_table[NR_fstatat64] = SyscallInfo("fstatat64", NR_fstatat64, 4, "%d, %p, %p, %d", self.sys_fstatat64)
        self.syscall_table[NR_mkdirat] = SyscallInfo("mkdirat", NR_mkdirat, 3, "%d, %p, %d", self.sys_mkdirat)
        self.syscall_table[NR_fchownat] = SyscallInfo("fchownat", NR_fchownat, 5, "%d, %p, %d, %d, %d", self.sys_fchownat)
        self.syscall_table[NR_fchmodat] = SyscallInfo("fchmodat", NR_fchmodat, 4, "%d, %p, %d, %d", self.sys_fchmodat)
        self.syscall_table[NR_renameat] = SyscallInfo("renameat", NR_renameat, 4, "%d, %p, %d, %p", self.sys_renameat)
        self.syscall_table[NR_unlinkat] = SyscallInfo("unlinkat", NR_unlinkat, 3, "%d, %p, %d", self.sys_unlinkat)
        self.syscall_table[NR_statfs64] = SyscallInfo("statfs64", NR_statfs64, 2, "%p, %p", self.sys_statfs64)
        self.syscall_table[NR_clock_gettime] = SyscallInfo("clock_gettime", NR_clock_gettime, 2, "%d, %p", self.sys_clock_gettime)
        self.syscall_table[NR_clock_settime] = SyscallInfo("clock_settime", NR_clock_settime, 2, "%d, %p", self.sys_clock_settime)
        self.syscall_table[NR_clock_getres] = SyscallInfo("clock_getres", NR_clock_getres, 2, "%d, %p", self.sys_clock_getres)
        self.syscall_table[NR_clock_nanosleep] = SyscallInfo("clock_nanosleep", NR_clock_nanosleep, 4, "%d, %d, %p, %p", self.sys_clock_nanosleep)
        self.syscall_table[NR_timer_create] = SyscallInfo("timer_create", NR_timer_create, 3, "%d, %p, %p", self.sys_timer_create)
        self.syscall_table[NR_timer_settime] = SyscallInfo("timer_settime", NR_timer_settime, 4, "%d, %d, %p, %p", self.sys_timer_settime)
        self.syscall_table[NR_timer_gettime] = SyscallInfo("timer_gettime", NR_timer_gettime, 2, "%d, %p", self.sys_timer_gettime)
        self.syscall_table[NR_timer_getoverrun] = SyscallInfo("timer_getoverrun", NR_timer_getoverrun, 1, "%d", self.sys_timer_getoverrun)
        self.syscall_table[NR_timer_delete] = SyscallInfo("timer_delete", NR_timer_delete, 1, "%d", self.sys_timer_delete)
        self.syscall_table[NR_utimes] = SyscallInfo("utimes", NR_utimes, 2, "%p, %p", self.sys_utimes)
        self.syscall_table[NR_socket] = SyscallInfo("socket", NR_socket, 3, "%d, %d, %d", self.sys_socket)
        self.syscall_table[NR_socketpair] = SyscallInfo("socketpair", NR_socketpair, 4, "%d, %d, %d, %p", self.sys_socketpair)
        self.syscall_table[NR_bind] = SyscallInfo("bind", NR_bind, 3, "%d, %p, %d", self.sys_bind)
        self.syscall_table[NR_connect] = SyscallInfo("connect", NR_connect, 3, "%d, %p, %d", self.sys_connect)
        self.syscall_table[NR_listen] = SyscallInfo("listen", NR_listen, 2, "%d, %d", self.sys_listen)
        self.syscall_table[NR_accept] = SyscallInfo("accept", NR_accept, 3, "%d, %p, %p", self.sys_accept)
        self.syscall_table[NR_getsockname] = SyscallInfo("getsockname", NR_getsockname, 3, "%d, %p, %p", self.sys_getsockname)
        self.syscall_table[NR_getpeername] = SyscallInfo("getpeername", NR_getpeername, 3, "%d, %p, %p", self.sys_getpeername)
        self.syscall_table[NR_sendto] = SyscallInfo("sendto", NR_sendto, 6, "%d, %p, %d, %d, %p, %d", self.sys_sendto)
        self.syscall_table[NR_recvfrom] = SyscallInfo("recvfrom", NR_recvfrom, 6, "%d, %p, %d, %d, %p, %p", self.sys_recvfrom)
        self.syscall_table[NR_shutdown] = SyscallInfo("shutdown", NR_shutdown, 2, "%d, %d", self.sys_shutdown)
        self.syscall_table[NR_setsockopt] = SyscallInfo("setsockopt", NR_setsockopt, 5, "%d, %d, %d, %p, %d", self.sys_setsockopt)
        self.syscall_table[NR_getsockopt] = SyscallInfo("getsockopt", NR_getsockopt, 5, "%d, %d, %d, %p, %p", self.sys_getsockopt)
        self.syscall_table[NR_sendmsg] = SyscallInfo("sendmsg", NR_sendmsg, 3, "%d, %p, %d", self.sys_sendmsg)
        self.syscall_table[NR_recvmsg] = SyscallInfo("recvmsg", NR_recvmsg, 3, "%d, %p, %d", self.sys_recvmsg)
        self.syscall_table[NR_epoll_create] = SyscallInfo("epoll_create", NR_epoll_create, 1, "%d", self.sys_epoll_create)
        self.syscall_table[NR_epoll_ctl] = SyscallInfo("epoll_ctl", NR_epoll_ctl, 4, "%d, %d, %d, %p", self.sys_epoll_ctl)
        self.syscall_table[NR_epoll_wait] = SyscallInfo("epoll_wait", NR_epoll_wait, 4, "%d, %p, %d, %d", self.sys_epoll_wait)
        self.syscall_table[NR_inotify_init] = SyscallInfo("inotify_init", NR_inotify_init, 0, "", self.sys_inotify_init)
        self.syscall_table[NR_inotify_add_watch] = SyscallInfo("inotify_add_watch", NR_inotify_add_watch, 3, "%d, %p, %d", self.sys_inotify_add_watch)
        self.syscall_table[NR_inotify_rm_watch] = SyscallInfo("inotify_rm_watch", NR_inotify_rm_watch, 2, "%d, %d", self.sys_inotify_rm_watch)
        self.syscall_table[NR_ARM_set_tls] = SyscallInfo("ARM_set_tls", NR_ARM_set_tls, 1, "%p", self.sys_ARM_set_tls)
        self.syscall_table[NR_ARM_cacheflush] = SyscallInfo("ARM_cacheflush", NR_ARM_cacheflush, 3, "%p, %p, %d", self.sys_ARM_cacheflush)

    def __align_stack__(self, p):
        """
        Align the stack to 8 bytes.
        """
        return Align(p, 8)

    def __stack_push__(self, sp, value):
        """
        Push a value to the current task stack.
        """
        sp, addr = self.__stack_alloc__(sp, 4)
        self.get_current_task().memory.set_dword(addr, value)
        return sp

    def __stack_alloc__(self, sp, len_):
        """
        Allocate @len_ bytes in the stack.
        """
        if self.stack_grows_down:
            sp -= len_
            return sp, sp

        else:
            old_sp = sp
            sp += len_
            return sp, old_sp

    def __vectors_user_mapping__(self):
        """
        Map userspace exception vector mappings.
        """
        start = 0xffff0000
        end = 0xffff0000 + PAGE_SIZE

        log.debug("Mapping ARM user space vector mappings [%.8x-%.8x]" % (start, end))

        ret = self.sys_mmap(start, PAGE_SIZE, PROT_READ | PROT_EXEC, MAP_FIXED | MAP_PRIVATE, 0, 0)
        if ret == -1:
            raise Exception("Could not map userspace ARM vectors.")

        return ret

    def __elf_plat_init__(self, load_addr):
        self.cpu.setRegister(ARMRegister.R0, 0)

    def __start_thread__(self, elf_entry, stack):
        """
        #define start_thread(regs,pc,sp)					\
        ({									                \
            unsigned long *stack = (unsigned long *)sp;		\
            set_fs(USER_DS);						        \
            memset(regs->uregs, 0, sizeof(regs->uregs));	\
            if (current->personality & ADDR_LIMIT_32BIT)	\
                regs->ARM_cpsr = USR_MODE;				    \
            else								            \
                regs->ARM_cpsr = USR26_MODE;				\
            if (elf_hwcap & HWCAP_THUMB && pc & 1)			\
                regs->ARM_cpsr |= PSR_T_BIT;				\
            regs->ARM_cpsr |= PSR_ENDSTATE;					\
            regs->ARM_pc = pc & ~1;		/* pc */			\
            regs->ARM_sp = sp;		/* sp */			    \
            regs->ARM_r2 = stack[2];	/* r2 (envp) */		\
            regs->ARM_r1 = stack[1];	/* r1 (argv) */		\
            regs->ARM_r0 = stack[0];	/* r0 (argc) */		\
            nommu_start_thread(regs);					    \
        })
        """
        # self.cpu.setCPSR(ARMProcessor.USR_MODE)

        # Set the processor mode.
        mode = ARMMode.THUMB if (elf_entry & 1) else ARMMode.ARM
        self.cpu.setCurrentMode(mode) 

        # TODO: Set endianess

        # Read the values from memory.
        envp = self.get_current_task().memory.get_dword(stack + 4 * 2)
        argv = self.get_current_task().memory.get_dword(stack + 4 * 1)
        argc = self.get_current_task().memory.get_dword(stack + 4 * 0)

        self.cpu.setRegister(ARMRegister.R2, envp)
        self.cpu.setRegister(ARMRegister.R1, argv)
        self.cpu.setRegister(ARMRegister.R0, argc)

        self.cpu.setRegister(ARMRegister.PC, elf_entry & ~1)
        self.cpu.setRegister(ARMRegister.SP, stack)

    def __get_syscall_arguments__(self, sys_info):
        args = []
        if sys_info.nargs == 1:
            args.append(self.cpu.getRegister(ARMRegister.R0))

        elif sys_info.nargs == 2:
            args.append(self.cpu.getRegister(ARMRegister.R0))
            args.append(self.cpu.getRegister(ARMRegister.R1))

        elif sys_info.nargs == 3:
            args.append(self.cpu.getRegister(ARMRegister.R0))
            args.append(self.cpu.getRegister(ARMRegister.R1))
            args.append(self.cpu.getRegister(ARMRegister.R2))

        elif sys_info.nargs == 4:
            args.append(self.cpu.getRegister(ARMRegister.R0))
            args.append(self.cpu.getRegister(ARMRegister.R1))
            args.append(self.cpu.getRegister(ARMRegister.R2))
            args.append(self.cpu.getRegister(ARMRegister.R3))

        elif sys_info.nargs == 5:
            args.append(self.cpu.getRegister(ARMRegister.R0))
            args.append(self.cpu.getRegister(ARMRegister.R1))
            args.append(self.cpu.getRegister(ARMRegister.R2))
            args.append(self.cpu.getRegister(ARMRegister.R3))
            args.append(self.cpu.getRegister(ARMRegister.R4))

        elif sys_info.nargs == 6:
            args.append(self.cpu.getRegister(ARMRegister.R0))
            args.append(self.cpu.getRegister(ARMRegister.R1))
            args.append(self.cpu.getRegister(ARMRegister.R2))
            args.append(self.cpu.getRegister(ARMRegister.R3))
            args.append(self.cpu.getRegister(ARMRegister.R4))
            args.append(self.cpu.getRegister(ARMRegister.R5))
        
        elif sys_info.nargs > 6:
            raise RuntimeError("Can't handle syscall of more than 6 arguments.")

        return args

    def __dispatch_syscall__(self):
        """
        Routine to dispatch syscalls to its handler.
        """
        sys_no = self.cpu.getRegister(ARMRegister.R7)
        sys_info = self.syscall_table[sys_no]
        args = self.__get_syscall_arguments__(sys_info)
        
        args_string = ", ".join(map(lambda x: "0x%.8x" % x, args))  
        log.info("Dispatching syscall %s(%s)" % (sys_info.name, args_string))
        
        ret = sys_info.handler(*args)
        
        # Set the return value in r0.
        self.cpu.setRegister(ARMRegister.R0, ret)
        
        log.info("Syscall %s returned %d" % (sys_info.name, ret))

def parse_emulee_arguments(args):
    try:
        emulee_args = args[args.index("--") + 1:]
    except ValueError:
        raise RuntimeError("Error, invalid arguments passed. See help.")
    
    idx = -1
    for i in xrange(0, len(emulee_args)):
        if "=" in emulee_args[i]:
            idx = i
    
    envp, argv, args = emulee_args[:idx + 1], emulee_args[idx + 1:], args[:args.index("--")] 
        
    return envp, argv, args

def main():
    parser = argparse.ArgumentParser(description='Userland binary emulator')
    parser.add_argument('program', type=str, metavar='PROGRAM', help='Program to emulate.')
    parser.add_argument('-d', '--debug', action='store_true', help='Print debugging information.')
    parser.add_argument('-r', '--root', type=str, help='Directory where all the needed libraries are placed.')
    parser.add_argument('-m', '--max', default=None, type=int, help='Maximum number of instructions to emulate.')
    parser.add_argument('--effects-all', default=[0], action='append_const', const=ARMEmulator.ALL_EFFECTS, dest="effects_mask", help='Show all instruction effects.')
    parser.add_argument('--effects-regs', default=[0], action='append_const', const=ARMEmulator.REG_EFFECTS, dest="effects_mask", help='Show register read & write accesses.')
    parser.add_argument('--effects-mem', default=[0], action='append_const', const=ARMEmulator.MEM_EFFECTS, dest="effects_mask", help='Show memory read & write accesses.')
    parser.add_argument('--effects-flags', default=[0], action='append_const', const=ARMEmulator.FLAG_EFFECTS, dest="effects_mask", help='Show flag read & write accesses.')
    
    log.info("ARM Linux userland emulator")

    # Parse the arguments and environment variables that we will pass to the emulee. 
    try:
        envp, argv, args = parse_emulee_arguments(sys.argv)
    except RuntimeError:
        parser.print_help()
        sys.exit(-1)        
    
    if len(envp):
        log.info("Using the following environment variables:")
        for env in envp:
            log.info("  %s" % env)

    log.info("Program arguments:")
    log.info("  " + "".join(argv))
    
    # Parse the arguments for the emulator.
    args = parser.parse_args(args=args)

    # Check that we've a binary to execute.
    if not args.program:
        log.error("I need a binary to execute\n")
        parser.print_help()
        sys.exit(-1)

    # If the user did not specify a root directory, the cwd is chosen.
    root_dir = os.path.realpath(args.root if args.root else os.getcwd())
    log.info("Using directory %s as the root directory for syscalls." % root_dir)
    
    # Enable debug if requested.
    debug = args.debug
    if debug:
        logging.basicConfig(level=logging.DEBUG)
        
    # Parse the effects mask if any.
    acum_mask = 0
    for value in args.effects_mask:
        acum_mask |= value
        
    settings = {}
    settings["show-effects"] = acum_mask != 0
    settings["effects-mask"] = acum_mask
    settings["max-instructions"] = args.max
    settings["root-dir"] = root_dir
    linux = ARMLinuxOS(settings)     
    
    try:   
        linux.execute(argv, envp)
    
    except InstructionNotImplementedException, e:
        log.error(e)
    
    except InvalidMemoryAccessException, e:
        log.error(e)
        
    except EmulationExited, e:
        log.info("Program exited")
    
    except MissingSyscallException, e:
        log.error("Missing syscall, please implement it: %s" % e)

if __name__ == "__main__":
    try:
        main()

    except RuntimeError, e:
        log.error("Error: %s" % e)

    except KeyboardInterrupt:
        log.error("Error: interrupted by the user")
