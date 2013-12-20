'''
Created on Dec 9, 2013

@author: anon
'''
NR_exit = 1
NR_fork = 2
NR_clone = 120
NR_execve = 11
NR_setuid32 = 213
NR_getuid32 = 199
NR_getgid32 = 200
NR_geteuid32 = 201
NR_getegid32 = 202
NR_getresuid32 = 209
NR_getresgid32 = 211
NR_gettid = 224
NR_getgroups32 = 205
NR_getpgid = 132
NR_getppid = 64
NR_setsid = 66
NR_setgid32 = 214
NR_setreuid32 = 203
NR_setresuid32 = 208
NR_setresgid32 = 210
NR_brk = 45
NR_ptrace = 26
NR_getpriority = 96
NR_setpriority = 97
NR_setrlimit = 75
NR_ugetrlimit = 191
NR_getrusage = 77
NR_setgroups32 = 206
NR_setpgid = 57
NR_setregid32 = 204
NR_chroot = 61
NR_prctl = 172
NR_capget = 184
NR_capset = 185
NR_sigaltstack = 186
NR_acct = 51
NR_read = 3
NR_write = 4
NR_pread64 = 180
NR_pwrite64 = 181
NR_open = 5
NR_close = 6
NR_lseek = 19
NRllseek = 140
NR_getpid = 20
NR_mmap2 = 192
NR_munmap = 91
NR_mremap = 163
NR_msync = 144
NR_mprotect = 125
NR_mlock = 150
NR_munlock = 151
NR_ioctl = 54
NR_readv = 145
NR_writev = 146
NR_fcntl = 55
NR_flock = 143
NR_fchmod = 94
NR_dup = 41
NR_pipe = 42
NR_dup2 = 63
NRnewselect = 142
NR_ftruncate = 93
NR_fsync = 118
NR_fchown32 = 207
NR_sync = 36
NR_fcntl64 = 221
NR_sendfile = 187
NR_link = 9
NR_unlink = 10
NR_chdir = 12
NR_mknod = 14
NR_chmod = 15
NR_chown32 = 212
NR_lchown32 = 198
NR_mount = 21
NR_umount2 = 52
NR_fstat64 = 197
NR_stat64 = 195
NR_lstat64 = 196
NR_mkdir = 39
NR_readlink = 85
NR_rmdir = 40
NR_rename = 38
NR_getcwd = 183
NR_access = 33
NR_symlink = 83
NR_fchdir = 133
NR_truncate = 92
NR_pause = 29
NR_gettimeofday = 78
NR_settimeofday = 79
NR_times = 43
NR_nanosleep = 162
NR_getitimer = 105
NR_setitimer = 104
NR_sigaction = 67
NR_sigprocmask = 126
NR_sigsuspend = 72
NR_rt_sigaction = 174
NR_rt_sigprocmask = 175
NR_rt_sigtimedwait = 177
NR_sigpending = 73
NR_sched_setscheduler = 156
NR_sched_getscheduler = 157
NR_sched_yield = 158
NR_sched_setparam = 154
NR_sched_getparam = 155
NR_sched_get_priority_max = 159
NR_sched_get_priority_min = 160
NR_sched_rr_get_interval = 161
NR_uname = 122
NR_wait4 = 114
NR_umask = 60
NR_reboot = 88
NR_syslog = 103
NR_init_module = 128
NR_delete_module = 129
NR_syslog = 103
NR_futex = 240
NR_poll = 168
NR_exit_group = 248
NR_waitid = 280
NR_vfork = 190
NR_openat = 322
NR_madvise = 220
NR_mincore = 219
NR_getdents64 = 217
NR_fstatfs64 = 267
NR_fstatat64 = 327
NR_mkdirat = 323
NR_fchownat = 325
NR_fchmodat = 333
NR_renameat = 329
NR_unlinkat = 328
NR_statfs64 = 266
NR_clock_gettime = 263
NR_clock_settime = 262
NR_clock_getres = 264
NR_clock_nanosleep = 265
NR_timer_create = 257
NR_timer_settime = 258
NR_timer_gettime = 259
NR_timer_getoverrun = 260
NR_timer_delete = 261
NR_utimes = 269
NR_socket = 281
NR_socketpair = 288
NR_bind = 282
NR_connect = 283
NR_listen = 284
NR_accept = 285
NR_getsockname = 286
NR_getpeername = 287
NR_sendto = 290
NR_recvfrom = 292
NR_shutdown = 293
NR_setsockopt = 294
NR_getsockopt = 295
NR_sendmsg = 296
NR_recvmsg = 297
NR_epoll_create = 250
NR_epoll_ctl = 251
NR_epoll_wait = 252
NR_inotify_init = 316
NR_inotify_add_watch = 317
NR_inotify_rm_watch = 318
NR_ARM_set_tls = 983045
NR_ARM_cacheflush = 983042