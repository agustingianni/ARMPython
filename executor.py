import os
import sys
import logging
import argparse
import shlex

from elftools.elf.elffile import ELFFile
from elftools.elf.constants import P_FLAGS
from disassembler.arch import ARMRegister, ARMMode
from emulator.memory import ConcreteMemoryMap, GetLastValidAddress
from emulator.ARMEmulator import ARMEmulator, ARMProcessor

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
    def __init__(self, *args, **kwargs):
        self.file = file(*args, **kwargs)

    def stat(self):
        return os.fstat(self.fileno())

    def ioctl(self, request, argp):
        # argp ignored..
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


class LinuxOS(object):
    def __init__(self, cpu, memory):
        """
        Emulate the behaviour of the Linux OS.

        The are platform specific bits should be implemented by inheriting
        this class and overriding the proper abstract methods.
        """
        # Set up the basic elements of the virtual machine.
        self.cpu = cpu

        # This is a map of all the tasks being executed.
        self.tasks = {}
        self.curr_task = Task(memory)

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


    def execute(self, binary, argv, envp):
        """
        Load the binary in memory and then call the interpreter
        to resolve what is needed. The interpreter will be emulated so
        we do not need to code anything.

        Implemented following binfmt_elf.c from the linux kernel.
        """
        interpreter = None

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
        stack_size = 8 * 1024
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

        # Align the stack since the strings may not be aligned.
        stack = ((stack - 4) / 4) * 4

        # Two null's. I have no idea why.
        # stack = self.__stack_push__(stack, 0)
        # stack = self.__stack_push__(stack, 0)

        # Mark the end of the vector.
        stack = self.__stack_push__(stack, 0x00000000)
        stack = self.__stack_push__(stack, AT_NULL)

        # String identifying CPU for optimizations.
        stack = self.__stack_push__(stack, 0x00000000)
        stack = self.__stack_push__(stack, AT_PLATFORM)  # f

        # Filename of program.
        stack = self.__stack_push__(stack, 0x00000000)
        stack = self.__stack_push__(stack, AT_EXECFN)  # 1f

        # Address of 16 random bytes.
        stack = self.__stack_push__(stack, 0x00000000)
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

        log.debug("Entry point: %.8x" % elf_entry)
        log.debug("Stack start: %.8x" % stack)
        log.debug("Brk        : %.8x" % elf_brk)

        # log.debug("Stack Dump:")
        # for addr, value in MemoryMapIterator(task.memory, start_addr=stack, end_addr=stack_top, step_size=4):
        #     log.debug("\t[%.8x] = %.8x" % (addr, task.memory.get_dword(addr)))

        # Setup special registers following per-architecture ABI.
        self.__elf_plat_init__(reloc_func_desc)

        self.__start_thread__(elf_entry, stack)
        
        # Let the CPU consume instructions and execute.
        self.cpu.run()


class ARMLinuxOS(LinuxOS):
    def __init__(self):
        """
        Emulate Linux running on an ARM processor.
        """
        memory = ConcreteMemoryMap()
        cpu = ARMEmulator(memory)
        self.stack_grows_down = True

        super(ARMLinuxOS, self).__init__(cpu, memory)


    def __align_stack__(self, p):
        """
        Align the stack to 8 bytes.
        """
        return p

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
        self.cpu.setCPSR(ARMProcessor.USR_MODE)

        # Set the processor mode.
        if elf_entry & 1:
            self.cpu.setCurrentMode(ARMMode.THUMB)

        else:
            self.cpu.setCurrentMode(ARMMode.ARM)

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


def parse_emulee_arguments(args):
    emulee_args = args[args.index("--") + 1:]
    
    idx = -1
    for i in xrange(0, len(emulee_args)):
        if "=" in emulee_args[i]:
            idx = i
    
    envp, argv, args = emulee_args[:idx+1], emulee_args[idx + 1:], args[:args.index("--")] 
        
    return envp, argv, args

def main():
    parser = argparse.ArgumentParser(description='Userland binary emulator')
    parser.add_argument('program', type=str, metavar='PROGRAM', help='Program to emulate.')
    parser.add_argument('-d', '--debug', action='store_true', help='Print debugging information.')
    parser.add_argument('-r', '--root', type=str, help='Directory where all the needed libraries are placed.')

    # Parse the arguments and environment variables that we will pass to the emulee. 
    envp, argv, args = parse_emulee_arguments(sys.argv)
    args = parser.parse_args(args=args)

    # Check that we've a binary to execute.
    if not args.program:
        log.info("I need a binary to execute\n")
        parser.print_help()
        sys.exit(-1)

    # Enable debug if requested.
    debug = args.debug
    if debug:
        logging.basicConfig(level=logging.DEBUG)

    sys.exit()


    linux = ARMLinuxOS()        
    linux.execute(args.program, argv, envp)


if __name__ == "__main__":
    try:
        main()

    except KeyboardInterrupt:
        pass
