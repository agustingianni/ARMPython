# ARMEncoding
eEncodingA1 = 0
eEncodingA2 = 1
eEncodingA3 = 2
eEncodingA4 = 3
eEncodingA5 = 4
eEncodingT1 = 5
eEncodingT2 = 6
eEncodingT3 = 7
eEncodingT4 = 8
eEncodingT5 = 9

ARMv4    = 1 << 0
ARMv4T   = 1 << 1
ARMv5T   = 1 << 2
ARMv5TE  = 1 << 3
ARMv5TEJ = 1 << 4
ARMv6    = 1 << 5
ARMv6K   = 1 << 6
ARMv6T2  = 1 << 7
ARMv7    = 1 << 8
ARMv7S   = 1 << 9
ARMv8    = 1 << 10
ARMvAll  = 0xffffffff

ARMv4All   = ARMv4   | ARMv4T
ARMv5TAll  = ARMv5T  | ARMv5TE  | ARMv5TEJ
ARMv5TEAll = ARMv5TE | ARMv5TEJ
ARMv6All   = ARMv6   | ARMv6K   | ARMv6T2
ARMv7All   = ARMv7   | ARMv7S
ARMv8All   = ARMv8

ARMV4T_ABOVE  = (ARMv4T   | ARMv5T   | ARMv5TE  | ARMv5TEJ | ARMv6   | ARMv6K  | ARMv6T2 | ARMv7  | ARMv7S | ARMv8)
ARMV5_ABOVE   = (ARMv5T   | ARMv5TE  | ARMv5TEJ | ARMv6    | ARMv6K  | ARMv6T2 | ARMv7   | ARMv7S | ARMv8)
ARMV5TE_ABOVE = (ARMv5TE  | ARMv5TEJ | ARMv6    | ARMv6K   | ARMv6T2 | ARMv7   | ARMv7S  | ARMv8)
ARMV5J_ABOVE  = (ARMv5TEJ | ARMv6    | ARMv6K   | ARMv6T2  | ARMv7   | ARMv7S  | ARMv8)
ARMV6_ABOVE   = (ARMv6    | ARMv6K   | ARMv6T2  | ARMv7    | ARMv7S  | ARMv8) 
ARMV6T2_ABOVE = (ARMv6T2  | ARMv7    | ARMv7S   | ARMv8)
ARMV7_ABOVE   = (ARMv7    | ARMv7S   | ARMv8)

No_VFP = 0
VFPv1 = (1 << 1)
VFPv2 = (1 << 2)
VFPv3 = (1 << 3)
AdvancedSIMD = (1 << 4)

VFPv1_ABOVE = (VFPv1 | VFPv2 | VFPv3 | AdvancedSIMD)
VFPv2_ABOVE = (VFPv2 | VFPv3 | AdvancedSIMD)
VFPv2v3 = (VFPv2 | VFPv3)

eSize16 = 0
eSize32 = 1

# ARM shifter types
SRType_LSL = 0 
SRType_LSR = 1
SRType_ASR = 2
SRType_ROR = 3
SRType_RRX = 4
SRType_Invalid = -1

class ARMFLag:
    N = 0
    Z = 1
    C = 2
    V = 3
    Q = 4

class ARMMode:
    THUMB = 0
    ARM = 1

# TODO: These should be instances of Register
class ARMRegister:
    """
    ARM core registers
    """
    R0 = 0
    R1 = 1
    R2 = 2
    R3 = 3
    R4 = 4
    R5 = 5
    R6 = 6
    R7 = 7
    R8 = 8
    R9 = 9
    R10 = SL = 10
    R11 = FP = 11
    R12 = IP = 12
    R13 = SP = 13
    R14 = LR = 14
    R15 = PC = 15

class ARMInstruction:
    adc_immediate = 0x0000
    adc_register = 0x0001
    adc_rsr = 0x0002
    add_immediate = 0x0003
    add_register = 0x0004
    add_rsr = 0x0005
    add_sp_plus_immediate = 0x0006
    add_sp_plus_register = 0x0007
    adr = 0x0008
    and_immediate = 0x0009
    and_register = 0x000a
    and_rsr = 0x000b
    asr_immediate = 0x000c
    asr_register = 0x000d
    b = 0x000e
    bic_immediate = 0x000f
    bic_register = 0x0010
    bic_rsr = 0x0011
    bkpt = 0x0012
    bl_immediate = 0x0013
    blx_register = 0x0014
    bx = 0x0015
    bxj = 0x0016
    cbz = 0x0017
    cdp = 0x0018
    clz = 0x0019
    cmn_immediate = 0x001a
    cmn_register = 0x001b
    cmn_rsr = 0x001c
    cmp_immediate = 0x001d
    cmp_register = 0x001e
    cmp_rsr = 0x001f
    dbg = 0x0020
    eor_immediate = 0x0021
    eor_register = 0x0022
    eor_rsr = 0x0023
    eret = 0x0024
    hvc = 0x0025
    it = 0x0026
    ldc_immediate = 0x0027
    ldc_literal = 0x0028
    ldmda = 0x0029
    ldmdb = 0x002a
    ldm_exception_return = 0x002b
    ldmia = 0x002c
    ldmib = 0x002d
    ldm_user_registers = 0x002e
    ldrb_immediate = 0x002f
    ldrb_literal = 0x0030
    ldrb_register = 0x0031
    ldrbt = 0x0032
    ldrex = 0x0033
    ldrexb = 0x0034
    ldrexd = 0x0035
    ldrexh = 0x0036
    ldr_immediate = 0x0037
    ldr_literal = 0x0038
    ldr_register = 0x0039
    ldrt = 0x003a
    lsl_immediate = 0x003b
    lsl_register = 0x003c
    lsr_immediate = 0x003d
    lsr_register = 0x003e
    mcr = 0x003f
    mcrr = 0x0040
    mla = 0x0041
    mls = 0x0042
    mov_immediate = 0x0043
    mov_register = 0x0044
    mov_rsr = 0x0045
    movt = 0x0046
    mrc = 0x0047
    mrrc = 0x0048
    mrs = 0x0049
    msr = 0x004a
    mul = 0x004b
    mull = 0x004c
    mvn_immediate = 0x004d
    mvn_register = 0x004e
    mvn_rsr = 0x004f
    nop = 0x0050
    orr_immediate = 0x0051
    orr_register = 0x0052
    orr_rsr = 0x0053
    pld = 0x0054
    pop = 0x0055
    push = 0x0056
    rfe = 0x0057
    ror_immediate = 0x0058
    ror_register = 0x0059
    rrx = 0x005a
    rsb_immediate = 0x005b
    rsb_register = 0x005c
    rsb_rsr = 0x005d
    rsc_immediate = 0x005e
    rsc_register = 0x005f
    rsc_rsr = 0x0060
    sat_add_and_sub = 0x0061
    sbc_immediate = 0x0062
    sbc_register = 0x0063
    sbc_rsr = 0x0064
    sev = 0x0065
    smc = 0x0066
    smla = 0x0067
    smlal = 0x0068
    smlalb = 0x0069
    smlaw = 0x006a
    smul = 0x006b
    smull = 0x006c
    smulw = 0x006d
    srs = 0x006e
    stc = 0x006f
    stmda = 0x0070
    stmdb = 0x0071
    stmia = 0x0072
    stmib = 0x0073
    stm_user_registers = 0x0074
    strb_immediate = 0x0075
    strb_register = 0x0076
    strbt = 0x0077
    strex = 0x0078
    strexb = 0x0079
    strexd = 0x007a
    strexh = 0x007b
    str_immediate = 0x007c
    str_reg = 0x007d
    strt = 0x007e
    sub_immediate = 0x007f
    sub_register = 0x0080
    sub_rsr = 0x0081
    subs_pc_lr = 0x0082
    sub_sp_minus_immediate = 0x0083
    sub_sp_minus_register = 0x0084
    svc = 0x0085
    swp = 0x0086
    teq_immediate = 0x0087
    teq_register = 0x0088
    teq_rsr = 0x0089
    tst_immediate = 0x008a
    tst_register = 0x008b
    tst_rsr = 0x008c
    umaal = 0x008d
    umlal = 0x008e
    umull = 0x008f
    wfe = 0x0090
    wfi = 0x0091
    yield_ = 0x0092
