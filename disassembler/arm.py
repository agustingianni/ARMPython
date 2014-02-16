"""
Some notes about the ARM architecture:

Seven major versions of the instruction set have been defined to date,
denoted by the version numbers 1 to 7. Of these, the first three 
versions are now obsolete.

ARMv7 provides three profiles:

    ARMv7-A Application     profile
    ARMv7-R Real-time       profile    
    ARMv7-M Microcontroller profile 

The ARM memory model:
The ARM architecture uses a single, flat address space of 232 8-bit bytes.
The address space is also regarded as 230 32-bit words or 231 16-bit halfwords.

ARM core registers
    In the application level view, an ARM processor has:
        - thirteen general-purpose32-bit registers, R0 to R12
        - three 32-bit registers, R13 to R15, that sometimes or always have a special use.

    Registers R13 to R15 are usually referred to by names that indicate their special uses:
    SP, the Stack Pointer: Register R13 is used as a pointer to the active stack.
    In Thumb code, most instructions cannot access SP.

    LR, the Link Register: Register R14 is used to store the return address from a subroutine
    When a BL or BLX instruction performs a subroutine call, LR is set to the subroutine return
    address.
    
     PC, the Program Counter: Register R15 is the program counter:
        - When executing an ARM instruction, PC reads as the address of the current instruction plus 8.
        - When executing a Thumb instruction, PC reads as the address of the current instruction plus 4.
        - Writing an address to PC causes a branch to that address. 
    In Thumb code, most instructions cannot access PC.


Changing between Thumb state and ARM state:

    A processor in Thumb state (that is, executing Thumb instructions) can enter ARM state (and change to
    executing ARM instructions) by executing any of the following instructions: BX, BLX, or an LDR or LDM that
    loads the PC.

    A processor in ARM state (that is, executing ARM instructions) can enter Thumb state (and change to
    executing Thumb instructions) by executing any of the same instructions.

    In ARMv7, a processor in ARM state can also enter Thumb state (and change to executing Thumb
    instructions) by executing an ADC, ADD, AND, ASR, BIC, EOR, LSL, LSR, MOV, MVN, ORR, ROR, RRX, RSB, RSC, SBC, or SUB
    instruction that has the PC as destination register and does not set the condition flags.
    
Conditional execution
    Most ARM instructions can be conditionally executed. This means that they only have their normal effect
    on the programmers model operation, memory and coprocessors if the N, Z, C and V flags in the APSR
    satisfy a condition specified in the instruction. If the flags do not satisfy this condition, the instruction acts
    as a NOP, that is, execution advances to the next instruction as normal, including any relevant checks for
    exceptions being taken, but has no other effect.
    
"""

from disassembler.constants.arm import *
from disassembler.utils.bits import get_bit, get_bits, CountTrailingZeros, BitCount, SignExtend32
from disassembler.utils.arm import BadReg, DecodeImmShift, DecodeImmShiftARM, DecodeImmShiftThumb
from disassembler.utils.arm import ThumbExpandImm, ThumbExpandImm_C, ARMExpandImm, ARMExpandImm_C
from disassembler.utils.arm import ThumbImm12
from disassembler.arch import Immediate, Instruction, InvalidInstructionEncoding, \
    ARMRegister, CoprocessorName, CoprocessorOpCode, CoprocessorRegister, \
    MemoryBarrierOption, ISBOption, FPSCR, QRegister, DRegister, SRegister
from disassembler.arch import UnpredictableInstructionException, InstructionNotImplementedException
from disassembler.arch import Memory, RegisterShift, Condition, RegisterSet
from disassembler.arch import UndefinedOpcode, Jump, Register
from disassembler.arch import ARMMode

# Mask the 'x' to indicate ignore bits of an opcode
def I(x):
    return (0x80000000 | x) 

I1 = I(1)
I2 = I(2)
I3 = I(3)
I4 = I(4)
I5 = I(5)
I6 = I(6)
I7 = I(7)
I8 = I(8)
I9 = I(9)

# Replicate the bits pattern in 'bits' a given ammount of 'times'
def Replicate(bits, bits_size, times):
    tmp = bits
    for i in xrange(times - 1):
        tmp = (tmp << bits_size) | bits
    return tmp

def VFPExpandImm(imm8, N):
    if N == 32:
        t = get_bit(imm8, 7)
        t = (t << 1) | (~(get_bit(imm8, 6)) & 1)
        t = (t << 5) | Replicate(get_bit(imm8, 6), 1, 5)
        t = (t << 6) | get_bits(imm8, 5, 0)
        t = (t << 19)
        
    else:
        t = get_bit(imm8, 7)
        t = (t << 1) | (~(get_bit(imm8, 6)) & 1)
        t = (t << 8) | Replicate(get_bit(imm8, 6), 1, 8)
        t = (t << 6) | get_bits(imm8, 5, 0)
        t = (t << 48)
    
    return t

def AdvSIMDExpandImm(op, cmode, imm8):
    cmode_31 = get_bits(cmode, 3, 1)
    if cmode_31 == 0b000:
        # imm64 = Replicate(Zeros(24):imm8, 2);
        testimm8 = False
        imm64 = Replicate(imm8, 32, 2)
    
    elif cmode_31 == 0b001:
        # imm64 = Replicate(Zeros(16):imm8:Zeros(8), 2);
        testimm8 = True
        imm64 = Replicate(imm8 << 8, 32, 2)

    elif cmode_31 == 0b010:
        # imm64 = Replicate(Zeros(8):imm8:Zeros(16), 2);
        testimm8 = True
        imm64 = Replicate(imm8 << 16, 32,  2)

    elif cmode_31 == 0b011:
        # imm64 = Replicate(imm8:Zeros(24), 2);
        testimm8 = True
        imm64 = Replicate(imm8 << 24, 32, 2)

    elif cmode_31 == 0b100:
        # imm64 = Replicate(Zeros(8):imm8, 4);
        testimm8 = False
        imm64 = Replicate(imm8, 16, 4)

    elif cmode_31 == 0b101:
        # imm64 = Replicate(imm8:Zeros(8), 4);
        testimm8 = True
        imm64 = Replicate(imm8 << 8, 16, 4)

    elif cmode_31 == 0b110:
        testimm8 = True
        if get_bit(cmode, 0) == 0:
            # imm64 = Replicate(Zeros(16):imm8:Ones(8), 2);
            imm64 = Replicate((imm8 << 8) | 0b11111111, 32, 2)
        
        else:
            # imm64 = Replicate(Zeros(8):imm8:Ones(16), 2);
            imm64 = Replicate((imm8 << 16) | 0b1111111111111111, 32, 2)

    elif cmode_31 == 0b111:
        testimm8 = False

        # if cmode<0> == '0' && op == '0' then
        #     imm64 = Replicate(imm8, 8);
        if get_bit(cmode, 0) == 0 and op == 0:
            imm64 = Replicate(imm8, 8, 8)

        if get_bit(cmode, 0) == 0 and op == 1:
            imm8a = Replicate(get_bit(imm8, 7), 1, 8)
            imm8b = Replicate(get_bit(imm8, 6), 1, 8)
            imm8c = Replicate(get_bit(imm8, 5), 1, 8) 
            imm8d = Replicate(get_bit(imm8, 4), 1, 8)
            imm8e = Replicate(get_bit(imm8, 3), 1, 8) 
            imm8f = Replicate(get_bit(imm8, 2), 1, 8)
            imm8g = Replicate(get_bit(imm8, 1), 1, 8) 
            imm8h = Replicate(get_bit(imm8, 0), 1, 8)

            # imm64 = imm8a:imm8b:imm8c:imm8d:imm8e:imm8f:imm8g:imm8h;
            imm64 = 0
            imm64 = (imm64 << 8) | imm8a
            imm64 = (imm64 << 8) | imm8b
            imm64 = (imm64 << 8) | imm8c
            imm64 = (imm64 << 8) | imm8d
            imm64 = (imm64 << 8) | imm8e
            imm64 = (imm64 << 8) | imm8f
            imm64 = (imm64 << 8) | imm8g
            imm64 = (imm64 << 8) | imm8h

        # if cmode<0> == '1' && op == '0' then
        #     imm32 = imm8<7>: NOT(imm8<6>) : Replicate(imm8<6>,5) : imm8<5:0> : Zeros(19);
        #     imm64 = Replicate(imm32, 2);
        if get_bit(cmode, 0) == 1 and op == 0:
            imm32 = get_bit(imm8, 7) | (~get_bit(imm8, 6) & 1)
            imm32 = (imm32 << 5) | Replicate(get_bit(imm8, 6), 1, 5)
            imm32 = (imm32 << 6) | get_bits(imm8, 5, 0)
            imm32 = (imm32 << 19)
            imm64 = Replicate(imm32, 32, 2)

        if get_bit(cmode, 0) == 1 and op == 1:
            raise UndefinedOpcode()

    if testimm8 and imm8 == 0:
        raise UnpredictableInstructionException()

    return imm64

# Return true if the ignore bit is set
def is_ignore(x):
    return (0x80000000 & x) != 0

def get_ignore_bits(x):
    return (0x7fffffff & x)

# Check that the decode mask sums 32 bits.
def check(decode_mask):
    t = map(get_ignore_bits, decode_mask)
    return sum(t) == 32

# Decode an opcode following a 'decode_mask'
def decode_opcode(opcode, decode_mask):
    # Check that we decode the full 32 bit values.
    # assert check(decode_mask) != False
    
    elems = []
    bit_pos = 31
    for mask in decode_mask:
        if is_ignore(mask):
            bit_pos -= get_ignore_bits(mask)
            continue
        
        elems.append(get_bits(opcode, bit_pos, bit_pos - mask + 1))
        bit_pos -= mask
        
    return elems

def memoize(func):
    cache = {}
    def wrap(*args):
        if args not in cache:
            cache[args] = func(*args)
        return cache[args]
    return wrap

class ARMDisassembler(object):
    SYNTAX_DEFAULT = 0
    SYNTAX_SIMPLE = 1
        
    def __init__(self, mode=ARMMode.ARM, arch=ARMv7):
        """
        @mode: THUMB / ARM, the default is ARM
        """
        self.mode = mode
        self.ITCounter = 0
        self.pc = 0
        self.syntax = ARMDisassembler.SYNTAX_DEFAULT
        
        self.arm_isa = arch
        
        self.__build_tables__()
        
        # opcode to instruction cache
        self.cache = {}
        
    def set_architecture(self, arch):
        self.arm_isa = arch
        
    def set_mode(self, mode):
        self.mode = mode

    def set_pc(self, pc):
        self.pc = pc

    def set_syntax(self, syntax):
        self.syntax = syntax

    def __build_tables__(self):
        """
        Build opcode decoding tables.
        """
        self.__build_arm_table__()
        self.__build_thumb_table__()

    def __build_thumb_table__(self):
        """
        Build thumb opcode to decoding function map.
        """
        self.thumb_table = \
        (
        (0xffbf0f00, 0xecbd0b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vpop),  # FIXME
        (0xffbf0f00, 0xecbd0a00, VFPv2 | VFPv3 | VFPv4, eEncodingT2, No_VFP, eSize32, self.decode_vpop),  # FIXME
        (0xffbf0f00, 0xed2d0b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vpush), # FIXME
        (0xffbf0f00, 0xed2d0a00, VFPv2 | VFPv3 | VFPv4, eEncodingT2, No_VFP, eSize32, self.decode_vpush), # FIXME
        (0xefb800b0, 0xef800010, AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vorr_immediate),    # FIXME
        (0xffb00f10, 0xef200110, AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vorr_register),     # FIXME
        (0xffb00f10, 0xff000110, AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_veor),  # FIXME        
        (0xfe100f00, 0xec100b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vldm),  # FIXME
        (0xfe100f00, 0xec100a00, VFPv2 | VFPv3 | VFPv4, eEncodingT2, No_VFP, eSize32, self.decode_vldm),  # FIXME
        (0xffb00f10, 0xef000110, AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vand_register), # FIXME
        (0xfe100f00, 0xec000b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vstm),  # FIXME
        (0xfe100f00, 0xec000a00, VFPv2 | VFPv3 | VFPv4, eEncodingT2, No_VFP, eSize32, self.decode_vstm),  # FIXME
        (0xefb800b0, 0xef800030, AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vmvn_immediate),    # FIXME
        (0xffb30f90, 0xffb00580, AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vmvn_register), # FIXME
        (0xfe100000, 0xec000000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_stc),   # FIXME       
        (0xffffffc0, 0x0000b280, ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_uxth),
        (0xfffff0c0, 0xfa1ff080, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_uxth),
        (0xffffffc0, 0x0000b240, ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_sxtb),
        (0xfffff0c0, 0xfa4ff080, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_sxtb),
        (0xfff08020, 0xf3400000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_sbfx),
        (0xfbe08000, 0xf0600000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_orn_immediate),
        (0xffe08000, 0xea600000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_orn_register),
        (0xffffffc0, 0x0000b200, ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_sxth),
        (0xfffff0c0, 0xfa0ff080, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_sxth),
        (0xffffffc0, 0x0000ba00, ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_rev),
        (0xfff0f0f0, 0xfa90f080, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_rev),
        (0xfe100000, 0xfc000000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_stc),
        (0xfff0f0c0, 0xfa50f080, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_uxtab),
        (0xfff0f0c0, 0xfa40f080, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_sxtab),
        (0xffb30f90, 0xffb20000, AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vswp),
        (0xfff0f0c0, 0xfa10f080, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_uxtah),
        (0xfff0f0c0, 0xfa00f080, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_sxtah),
        (0xfff0f0f0, 0xfa90f0a0, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_rbit),
        (0xffd08020, 0xf3000000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ssat),
        (0xffff0fff, 0xeef10a10, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vmrs),
        (0xff300f00, 0xed000b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vstr),
        (0xff300f00, 0xed000a00, VFPv2 | VFPv3 | VFPv4, eEncodingT2, No_VFP, eSize32, self.decode_vstr),
        (0xffe00f00, 0xed100b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingT1, No_VFP, eSize32, self.decode_vldr),
        (0xff300f00, 0xed100a00, VFPv2 | VFPv3 | VFPv4, eEncodingT2, No_VFP, eSize32, self.decode_vldr),
        (0xffff8020, 0xf36f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_bfc),
        (0xfff08020, 0xf3600000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_bfi),
        (0xff000010, 0xee000000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_cdp),
        (0xff000010, 0xfe000000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_cdp),
        (0xffffffff, 0xf3bf8f2f, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_clrex),
        (0xffffffe8, 0x0000b660, ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_cps),
        (0xfffff800, 0xf3af8000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_cps),
        (0xfffffff0, 0xf3bf8f50, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_dmb),
        (0xfffffff0, 0xf3bf8f40, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_dsb),
        (0xffffff00, 0xf3bf8f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_eret),
        (0xfff0f000, 0xf7e08000, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_hvc),
        (0xfffffff0, 0xf3bf8f60, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_isb),
        (0xfe100000, 0xec100000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldc_immediate),
        (0xfffffff0, 0xfc100000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldc_immediate),
        (0xfe1f0000, 0xec1f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldc_literal),
        (0xfe1f0000, 0xfc1f0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldc_literal),
        (0xfe500000, 0xe8500000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrd_immediate),
        (0xfe5f0000, 0xe85f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrd_literal),
        (0xff7f0000, 0xf83f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrh_literal),
        (0xfff00f00, 0xf8300e00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrht),
        (0xfff00000, 0xf9900000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrsb_immediate),
        (0xfff00800, 0xf9100800, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldrsb_immediate),
        (0xff7f0000, 0xf91f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrsb_literal),
        (0xfffffe00, 0x00005600, ARMv4T, ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrsb_register),
        (0xfff00fc0, 0xf9100000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldrsb_register),
        (0xfff00f00, 0xf9100f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrsbt),
        (0xfff00000, 0xf9b00000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrsh_immediate),
        (0xfff00800, 0xf9300800, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldrsh_immediate),
        (0xff7f0000, 0xf93f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrsh_literal),
        (0xfffffe00, 0x00005e00, ARMv4T, ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrsh_register),
        (0xfff00fc0, 0xf9300000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldrsh_register),
        (0xfff00f00, 0xf9300e00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrsht),
        
        #(0xffffffef, 0xf3bf8f0f, ThumbEE, eEncodingT1, No_VFP, eSize32, self.decode_enterx_leavex),
         
        # VMOV (between two ARM core registers and a doubleword extension register)
        (0xffe00fd0, 0xec400b10, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_vmov_between_two_arm_core_registers_and_a_double_word_extension_register),
        
        # VMOV (between two ARM core registers and two single-precision registers)
        (0xffe00fd0, 0xec400a10, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_vmov_between_two_arm_core_registers_and_two_single_precision_registers),
        
        # VMOV (between ARM core register and single-precision register) 
        (0xffe00f7f, 0xee000a10, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_vmov_between_arm_core_register_and_single_precision_register),
        
        # VMOV (scalar to ARM core register)
        (0xff100f1f, 0xee100b10, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_vmov_scalar_to_arm_core_register),
         
        # VMOV (ARM core register to scalar)
        (0xff900f1f, 0xee000b10, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_vmov_arm_core_register_to_scalar),
         
        # VMOV register Advanced SIMD
        (0xffb00f10, 0xef200110, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_vmov_register),

        # VMOV register Advanced SIMD
        (0xffbf0ed0, 0xeeb00a40, ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_vmov_register),
         
        # VMOV Advanced SIMD
        (0xefb80090, 0xef800010, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_vmov_immediate),

        # VMOV Advanced SIMD
        (0xffb00ef0, 0xeeb00a00, ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_vmov_immediate),

        # CLREX ARMv7
        (0xffffffff, 0xf3bf8f2f, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_clrex),
         
        # adc (immediate) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf1400000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_adc_immediate),
        
        # adc (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004140, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_adc_register),
        
        # adc (register) ARMv6T2 | ARMv7
        (0xffe08000, 0xeb400000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_adc_register),
    
        # ADD (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x00001c00, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_add_immediate_thumb),
        
        # ADD (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00003000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_add_immediate_thumb),
        
        # ADD (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf1000000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_add_immediate_thumb),
        
        # ADD (immediate, Thumb) ARMv6T2 | ARMv7  
        (0xfbf08000, 0xf2000000, ARMv6T2 | ARMv7, eEncodingT4, No_VFP, eSize32, self.decode_add_immediate_thumb),
        
        # ADD (register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x00001800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_add_register_thumb),
        
        # ADD (register, Thumb) ARMv6T2 | ARMv7 if <Rdn> and <Rm> are both from R0-R7, ARMv4T | ARMv5TAll | ARMv6All | ARMv7 otherwise
        (0xffffff00, 0x00004400, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_add_register_thumb),
        
        # ADD (register, Thumb) ARMv6T2 | ARMv7
        (0xffe08000, 0xeb000000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_add_register_thumb),
        
        # ADD (SP plus immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x0000a800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_add_sp_plus_immediate),
        
        # ADD (SP plus immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffff80, 0x0000b000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_add_sp_plus_immediate),
        
        # ADD (SP plus immediate) ARMv6T2 | ARMv7
        (0xfbef8000, 0xf10d0000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_add_sp_plus_immediate),
        
        # ADD (SP plus immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0xfbff8000, 0xf20d0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingT4, No_VFP, eSize32, self.decode_add_sp_plus_immediate),
        
        # ADD (SP plus register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffff78, 0x00004468, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_add_sp_plus_register_thumb),

        # ADD (SP plus register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffff87, 0x00004485, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_add_sp_plus_register_thumb),
        
        # ADD (SP plus register, Thumb) ARMv6T2 | ARMv7
        (0xffef8000, 0xeb0d0000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_add_sp_plus_register_thumb),
        
        # ADR ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x0000a000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_adr),
        
        # ADR ARMv6T2 | ARMv7
        (0xfbff8000, 0xf2af0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_adr),
        
        # ADR ARMv6T2 | ARMv7
        (0xfbff8000, 0xf20f0000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_adr),
        
        # AND (immediate) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf0000000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_and_immediate),
        
        # AND (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_and_register),
        
        # AND (register) ARMv6T2 | ARMv7
        (0xffe08000, 0xea000000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_and_register),
        
        # ASR (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00001000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_asr_immediate),
        
        # ASR (immediate) ARMv6T2 | ARMv7
        (0xffef8030, 0xea4f0020, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_asr_immediate),
        
        # ASR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004100, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_asr_register),
        
        # ASR (register) ARMv6T2 | ARMv7
        (0xffe0f0f0, 0xfa40f000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_asr_register),

        # B ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff000, 0x0000d000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_b),
        
        # B ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x0000e000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_b),
        
        # B ARMv6T2 | ARMv7
        (0xf800d000, 0xf0008000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_b),
        
        # B ARMv6T2 | ARMv7
        (0xf800d000, 0xf0009000, ARMv6T2 | ARMv7, eEncodingT4, No_VFP, eSize32, self.decode_b),

        # BIC (immediate) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf0200000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_bic_immediate),
        
        # BIC (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004380, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_bic_register),
        
        # BIC (register) ARMv6T2 | ARMv7
        (0xffe08000, 0xea200000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_bic_register),

        # BKPT ARMv5TAll | ARMv6All | ARMv7
        (0xffffff00, 0x0000be00, ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_bkpt),
        
        # BL, BLX (immediate)
        # ARMv4T | ARMv5TAll | ARMv6All | ARMv7 if J1 == J2 == 1
        (0xf800f800, 0xf000f800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_bl_immediate),
        
        # BL, BLX (immediate)
        # ARMv6T2 | ARMv7 otherwise
        (0xf800d000, 0xf000d000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_bl_immediate),
        
        # BL, BLX (immediate)
        # ARMv5TAll | ARMv6All | ARMv7 if J1 == J2 == 1
        (0xf800e800, 0xf000e800, ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_bl_immediate),
        
        # BL, BLX (immediate)
        # ARMv6T2 | ARMv7 otherwise
        (0xf800c000, 0xf000c000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_bl_immediate),
                
        # BLX (register) ARMv5TAll | ARMv6All | ARMv7
        (0xffffff87, 0x00004780, ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_blx_register),
        
        # BX ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffff87, 0x00004700, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_bx),
        
        # BXJ ARMv6T2 | ARMv7
        (0xfff0ffff, 0xf3c08f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_bxj),
        
        # CBNZ, CBZ  ARMv6T2 | ARMv7
        (0xfffff500, 0x0000b100, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_cbz),
                
        # CLZ ARMv6T2 | ARMv7
        (0xfff0f0f0, 0xfab0f080, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_clz),

        # CMN (immediate) ARMv6T2 | ARMv7
        (0xfbf08f00, 0xf1100f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_cmn_immediate),
        
        # CMN (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x000042c0, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_cmn_register),
        
        # CMN (register) ARMv6T2 | ARMv7
        (0xfff08f00, 0xeb100f00, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_cmn_register),

        # CMP (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00002800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_cmp_immediate),
        
        # CMP (immediate) ARMv6T2 | ARMv7
        (0xfbf08f00, 0xf1b00f00, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_cmp_immediate),
        
        # CMP (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004280, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_cmp_register),
        
        # CMP (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffff00, 0x00004500, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_cmp_register),
                
        # CMP (register) ARMv6T2 | ARMv7
        (0xfff08f00, 0xebb00f00, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_cmp_register),
         
        # DBG ARMv7 (executes as NOP in ARMv6T2)
        (0xfffffff0, 0xf3af80f0, ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_dbg),
        
        # EOR (immediate) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf0800000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_eor_immediate),
        
        # EOR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004040, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_eor_register),
        
        # EOR (register) ARMv6T2 | ARMv7
        (0xffe08000, 0xea800000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_eor_register),
        
        # IT ARMv6T2 | ARMv7
        (0xffffff00, 0x0000bf00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_it),
        
        # LDM/LDMIA/LDMFD (Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7 (not in ThumbEE)
        (0xfffff800, 0x0000c800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_ldmia_thumb),

        # LDM/LDMIA/LDMFD (Thumb) ARMv6T2 | ARMv7
        (0xffd02000, 0xe8900000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldmia_thumb),
        
        # LDMDB/LDMEA ARMv6T2 | ARMv7
        (0xffd00000, 0xe9100000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldmdb),
        
        # LDR (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00006800, ARMV4T_ABOVE, eEncodingT1, No_VFP, eSize16, self.decode_ldr_immediate_thumb),
        
        # LDR (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00009800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_ldr_immediate_thumb),
        
        # LDR (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfff00000, 0xf8d00000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_ldr_immediate_thumb),
        
        # LDR (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfff00800, 0xf8500800, ARMv6T2 | ARMv7, eEncodingT4, No_VFP, eSize32, self.decode_ldr_immediate_thumb),

        # LDRH (immediate, Thumb) ARMv4T, ARMv5T*, ARMv6*, ARMv7
        (0xfffff800, 0x00008800, ARMV4T_ABOVE, eEncodingT1, No_VFP, eSize16, self.decode_ldrh_immediate_thumb),
        
        # LDRH (immediate, Thumb) ARMv6T2, ARMv7
        (0xfff00000, 0xf8b00000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldrh_immediate_thumb),
        
        # LDRH (immediate, Thumb) ARMv6T2, ARMv7
        (0xfff00800, 0xf8300800, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_ldrh_immediate_thumb),
        
        # LDRH (register, Thumb) ARMv4T, ARMv5T*, ARMv6*, ARMv7
        (0xfffffe00, 0x00005a00, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_ldrh_register_thumb),

        # LDRH (register, Thumb) ARMv6T2, ARMv7
        (0xfff00fc0, 0xf8300000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldrh_register_thumb),
                       
        # LDR (literal) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00004800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_ldr_literal),
        
        # LDR (literal) ARMv6T2 | ARMv7
        (0xff7f0000, 0xf85f0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldr_literal),
        
        # LDRH (literal, Thumb) ARMv6T2, ARMv7
        (0xff7f0000, 0xf83f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrh_literal_thumb),
        
        # LDR (register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x00005800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_ldr_register_thumb),
        
        # LDR (register, Thumb) ARMv6T2 | ARMv7
        (0xfff00fc0, 0xf8500000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldr_register_thumb),
        
        # LDRB (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00007800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_ldrb_immediate_thumb),
        
        # LDRB (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfff00000, 0xf8900000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldrb_immediate_thumb),
        
        # LDRB (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfff00800, 0xf8100800, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_ldrb_immediate_thumb),
        
        # LDRB (literal) ARMv6T2 | ARMv7
        (0xff7f0000, 0xf81f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrb_literal),
        
        # LDRB (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x00005c00, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_ldrb_register),
        
        # LDRB (register) ARMv6T2 | ARMv7
        (0xfff00fc0, 0xf8100000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ldrb_register),
        
        # LDRBT ARMv6T2 | ARMv7
        (0xfff00f00, 0xf8100e00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrbt),
        
        # LDREX ARMv6T2 | ARMv7
        (0xfff00f00, 0xe8500f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrex),
        
        # LDREXB ARMv7
        (0xfff00fff, 0xe8d00f4f, ARMV6T2_ABOVE, eEncodingT1, No_VFP, eSize32, self.decode_ldrexb),
        
        # LDREXD ARMv7
        (0xfff000ff, 0xe8d0007f, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrexd),
        
        # LDREXH ARMv7
        (0xfff00fff, 0xe8d00f5f, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrexh),
        
        # LDRT ARMv6T2 | ARMv7
        (0xfff00f00, 0xf8500e00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ldrt),

        # LSL (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00000000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_lsl_immediate),
        
        # LSL (immediate) ARMv6T2 | ARMv7
        (0xffef8030, 0xea4f0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_lsl_immediate),
        
        # LSL (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004080, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_lsl_register),
        
        # LSL (register) ARMv6T2 | ARMv7
        (0xffe0f0f0, 0xfa00f000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_lsl_register),
        
        # LSR (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00000800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_lsr_immediate),
        
        # LSR (immediate) ARMv6T2 | ARMv7
        (0xffef8030, 0xea4f0010, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_lsr_immediate),
        
        # LSR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x000040c0, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_lsr_register),
        
        # LSR (register) ARMv6T2 | ARMv7
        (0xffe0f0f0, 0xfa20f000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_lsr_register),

        # MLA ARMv6T2 | ARMv7
        (0xfff000f0, 0xfb000000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_mla),
        
        # MOV (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00002000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_mov_immediate),
        
        # MOV (immediate) ARMv6T2 | ARMv7
        (0xfbef8000, 0xf04f0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_mov_immediate),
        
        # MOV (immediate) ARMv6T2 | ARMv7 
        (0xfbf08000, 0xf2400000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_mov_immediate),

        # TODO: CHECK THIS
        # MOV (register, Thumb) ARMv6All | ARMv7 if <Rd> and <Rm> both from R0-R7
        # ARMv4T | ARMv5TAll | ARMv6All | ARMv7 otherwise
        (0xffffff00, 0x00004600, ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_mov_register_thumb),
        
        # MOV (register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00000000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_mov_register_thumb),
        
        # MOV (register, Thumb) ARMv6T2 | ARMv7
        (0xffeff0f0, 0xea4f0000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_mov_register_thumb),

        # MOVT ARMv6T2 | ARMv7
        (0xfbf08000, 0xf2c00000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_movt),
        
        # MUL ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004340, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_mul),
        
        # MUL ARMv6T2 | ARMv7
        (0xfff0f0f0, 0xfb00f000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_mul),

        # MVN (immediate) ARMv6T2 | ARMv7
        (0xfbef8000, 0xf06f0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_mvn_immediate),

        # MVN (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x000043c0, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_mvn_register),
        
        # MVN (register) ARMv6T2 | ARMv7
        (0xffef8000, 0xea6f0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_mvn_register),
        
        # NOP ARMv6T2 | ARMv7
        (0xffffffff, 0x0000bf00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_nop),

        # NOP ARMv6T2 | ARMv7
        (0xffffffff, 0xf3af8000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_nop),

        # ORR (immediate) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf0400000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_orr_immediate),
        
        # ORR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004300, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_orr_register),
        
        # ORR (register) ARMv6T2 | ARMv7
        (0xffe08000, 0xea400000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_orr_register),

        # POP (thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x0000bc00, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_pop_thumb),

        # POP (thumb) ARMv6T2 | ARMv7
        (0xffff2000, 0xe8bd0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_pop_thumb),

        # POP (thumb) ARMv6T2 | ARMv7
        (0xffff0fff, 0xf85d0b04, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_pop_thumb),
        
        # PLD, PLDW (immediate) 
        (0xffd0f000, 0xf890f000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_pld),
        (0xffd0ff00, 0xf810fc00, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_pld),

        # PUSH ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x0000b400, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_push),
        
        # PUSH ARMv6T2 | ARMv7
        (0xffffa000, 0xe92d0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_push),
        
        # PUSH ARMv6T2 | ARMv7
        (0xffff0fff, 0xf84d0d04, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_push),

        # RFE ARMv6T2 | ARMv7
        (0xffd0ffff, 0xe810c000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_rfe),
        
        # RFE ARMv6T2 | ARMv7
        (0xffd0ffff, 0xe990c000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_rfe),

        # ROR (immediate) ARMv6T2 | ARMv7
        (0xffef8030, 0xea4f0030, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ror_immediate),
        
        # ROR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x000041c0, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_ror_register),
        
        # ROR (register) ARMv6T2 | ARMv7
        (0xffe0f0f0, 0xfa60f000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_ror_register),
        
        # RRX ARMv6T2 | ARMv7
        (0xffeff0f0, 0xea4f0030, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_rrx),

        # RSB (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004240, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_rsb_immediate),
        
        # RSB (immediate) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf1c00000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_rsb_immediate),
        
        # RSB (register) ARMv6T2 | ARMv7
        (0xffe08000, 0xebc00000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_rsb_register),

        # SBC (immediate) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf1600000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_sbc_immediate),
        
        # TBB, TBH ARMv6T2 | ARMv7
        (0xfff0ffe0, 0xe8d0f000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_tb),
        
        # SBC (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004180, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_sbc_register),
        
        # SBC (register) ARMv6T2 | ARMv7
        (0xffe08000, 0xeb600000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_sbc_register),

        # SEV ARMv7 (executes as NOP in ARMv6T2)
        (0xffffffff, 0x0000bf40, ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_sev),

        # SEV ARMv7 (executes as NOP in ARMv6T2)
        (0xffffffff, 0xf3af8000, ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_sev),

        # SMLABB, SMLABT, SMLATB, SMLATT ARMv6T2 | ARMv7
        (0xfff000c0, 0xfb100000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_smla),
        
        # SMLALBB, SMLALBT, SMLALTB, SMLALTT ARMv6T2 | ARMv7
        (0xfff000c0, 0xfbc00080, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_smlal),
        
        # SMLAWB, SMLAWT ARMv6T2 | ARMv7
        (0xfff000e0, 0xfb300000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_smlaw),
        
        # SMULBB, SMULBT, SMULTB, SMULTT ARMv6T2 | ARMv7
        (0xfff0f0c0, 0xfb10f000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_smul),
        
        # SMULL ARMv6T2 | ARMv7
        (0xfff000f0, 0xfb800000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_smull),
        
        # SMULWB, SMULWT ARMv6T2 | ARMv7
        (0xfff0f0e0, 0xfb30f000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_smulw),
        
        # SRS, Thumb ARMv6T2 | ARMv7
        (0xffdfffe0, 0xe80dc000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_srs_thumb),
        
        # SRS, Thumb ARMv6T2 | ARMv7
        (0xffdfffe0, 0xe98dc000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_srs_thumb),
        
        # STM (STMIA, STMEA) ARMv4T | ARMv5TAll | ARMv6All | ARMv7 (not in ThumbEE)
        (0xfffff800, 0x0000c000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_stmia),
        
        # STM (STMIA, STMEA) ARMv6T2 | ARMv7
        (0xffd0a000, 0xe8800000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_stmia),
        
        # STMDB (STMFD) ARMv6T2 | ARMv7
        (0xffd0a000, 0xe9000000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_stmdb),
        
        # STR (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00006000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_str_immediate_thumb),
        
        # STR (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00009000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_str_immediate_thumb),
        
        # STR (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfff00000, 0xf8c00000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_str_immediate_thumb),
        
        # STR (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfff00800, 0xf8400800, ARMv6T2 | ARMv7, eEncodingT4, No_VFP, eSize32, self.decode_str_immediate_thumb),
        
        # STR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x00005000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_str_reg),
         
        # STR (register) ARMv6T2 | ARMv7
        (0xfff00fc0, 0xf8400000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_str_reg),
        
        # STRB (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00007000, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_strb_immediate_thumb),
        
        # STRB (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfff00000, 0xf8800000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_strb_immediate_thumb),
        
        # STRB (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfff00800, 0xf8000800, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_strb_immediate_thumb),
        
        # STRB (register) ARMv6T2 | ARMv7
        (0xfffffe00, 0x00005400, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_strb_register),

        # STRB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0xfff00fc0, 0xf8000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_strb_register),

        # STRBT ARMv6T2 | ARMv7
        (0xfff00f00, 0xf8000e00, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_strbt),
        
        # STREX ARMv6T2 | ARMv7
        (0xfff00000, 0xe8400000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_strex),

        # STREXB ARMv7
        (0xfff00ff0, 0xe8c00f40, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_strexb),

        # STREXD ARMv7
        (0xfff000f0, 0xe8c00070, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_strexd),

        # STREXH ARMv7
        (0xfff00ff0, 0xe8c00f50, ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_strexh),
        
        # STRT ARMv6T2 | ARMv7
        (0xfff00f00, 0xf8400e00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_strt),
        
        # SUB (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x00001e00, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_sub_immediate_thumb),
        
        # SUB (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffff800, 0x00003800, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT2, No_VFP, eSize16, self.decode_sub_immediate_thumb),
        
        # SUB (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfbe08000, 0xf1a00000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_sub_immediate_thumb),
        
        # SUB (immediate, Thumb) ARMv6T2 | ARMv7
        (0xfbf08000, 0xf2a00000, ARMv6T2 | ARMv7, eEncodingT4, No_VFP, eSize32, self.decode_sub_immediate_thumb),
        
        # SUB (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xfffffe00, 0x00001a00, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_sub_register),
        
        # SUB (register) ARMv6T2 | ARMv7
        (0xffe08000, 0xeba00000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_sub_register),
        
        # SUB (SP minus immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffff80, 0x0000b080, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_sub_sp_minus_immediate),

        # SUB (SP minus immediate) ARMv6T2 | ARMv7
        (0xfbef8000, 0xf1ad0000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_sub_sp_minus_immediate),
        
        # SUB (SP minus immediate) ARMv6T2 | ARMv7
        (0xfbff8000, 0xf2ad0000, ARMv6T2 | ARMv7, eEncodingT3, No_VFP, eSize32, self.decode_sub_sp_minus_immediate),
        
        # SUB (SP minus register) ARMv6T2 | ARMv7
        (0xffef8000, 0xebad0000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_sub_sp_minus_register),
        
        # SUBS PC, LR, Thumb ARMv6T2 | ARMv7
        (0xffffff00, 0xf3de8f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_subs_pc_lr_thumb),
        
        # SVC (previously SWI) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffff00, 0x0000df00, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_svc),
        
        # TEQ (immediate) ARMv6T2 | ARMv7
        (0xfbf08f00, 0xf0900f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_teq_immediate),
        
        # TEQ (register) ARMv6T2 | ARMv7
        (0xfff08f00, 0xea900f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_teq_register),
        
        # TST (immediate) ARMv6T2 | ARMv7
        (0xfbf08f00, 0xf0100f00, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_tst_immediate),
        
        # TST (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0xffffffc0, 0x00004200, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_tst_register),
        
        # TST (register) ARMv6T2 | ARMv7
        (0xfff08f00, 0xea100f00, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_tst_register),
        
        # UMAAL ARMv6T2 | ARMv7
        (0xfff000f0, 0xfbe00060, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_umaal),
    
        # UMLAL ARMv6T2 | ARMv7
        (0xfff000f0, 0xfbe00000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_umlal),
    
        # MULL ARMv6T2 | ARMv7
        (0xfff000f0, 0xfba00000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_mull),
    
        # WFE ARMv7 (executes as NOP in ARMv6T2)
        (0xffffffff, 0x0000bf20, ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_wfe),
        
        # WFE ARMv7 (executes as NOP in ARMv6T2)
        (0xffffffff, 0xf3af8002, ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_wfe),
        
        # WFI ARMv7 (executes as NOP in ARMv6T2)
        (0xffffffff, 0x0000bf30, ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_wfi),

        # WFI ARMv7 (executes as NOP in ARMv6T2)
        (0xffffffff, 0xf3af8003, ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_wfi),

        # YIELD ARMv7 (executes as NOP in ARMv6T2)
        (0xffffffff, 0x0000bf10, ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_yield),
        
        # YIELD ARMv7 (executes as NOP in ARMv6T2)
        (0xffffffff, 0xf3af8001, ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_yield),

        # UBFX ARMv6T2, ARMv7
        (0xfff08020, 0xf3c00000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_ubfx),
        
        # UXTB ARMv6*, ARMv7 
        (0xffffffc0, 0x0000b2c0, ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_uxtb),
        
        # UXTB ARMv6T2, ARMv7
        (0xfffff0c0, 0xfa5ff080, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_uxtb),

        # MRC ARMv6T2, ARMv7 
        (0xff100010, 0xee100010, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_mrc),

        # MRC ARMv6T2, ARMv7
        (0xff100010, 0xfe100010, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_mrc),
                
        # BFI ARMv6T2, ARMv7
        (0xfff08020, 0xf3600000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_bfi),

        # CDP ARMv6T2, ARMv7
        (0xff000010, 0xee000000, ARMv6T2 | ARMv7, eEncodingT1, No_VFP, eSize32, self.decode_cdp),

        # CDP ARMv6T2, ARMv7
        (0xff000010, 0xfe000000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_cdp),

        # CPS ARMv6*, ARMv7
        (0xffffffe8, 0x0000b660, ARMv6All | ARMv7, eEncodingT1, No_VFP, eSize16, self.decode_cps),

        # CPS ARMv6T2, ARMv7
        (0xfffff800, 0xf3af8000, ARMv6T2 | ARMv7, eEncodingT2, No_VFP, eSize32, self.decode_cps),

        # LAST
        (0x00000000, 0x00000000, ARMvAll, eEncodingT1, No_VFP, eSize32, self.decode_unknown),
        )

    def __build_arm_table__(self):        
        """
        Build arm opcode to decoding function map.
        """
        self.arm_table = \
        (
        (0x0fff03f0, 0x06ff0070, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_uxth),
        (0x0fbf0f00, 0x0cbd0b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vpop),
        (0x0fbf0f00, 0x0cbd0a00, VFPv2 | VFPv3 | VFPv4, eEncodingA2, No_VFP, eSize32, self.decode_vpop),
        (0x0fbf0f00, 0x0d2d0b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vpush),
        (0x0fbf0f00, 0x0d2d0a00, VFPv2 | VFPv3 | VFPv4, eEncodingA2, No_VFP, eSize32, self.decode_vpush),
        (0x0fff03f0, 0x06af0070, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_sxtb),
        (0x0fe00070, 0x07a00050, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_sbfx),
        (0x0fff03f0, 0x06bf0070, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_sxth),
        (0xfeb800b0, 0xf2800010, AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vorr_immediate),
        (0xffb30f10, 0xf3b00600, AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vorr_register),
        (0xffb00f10, 0xf3000110, AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_veor),
        (0x0fff0ff0, 0x06bf0f30, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_rev),
        (0x0e100f00, 0x0c100b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vldm),
        (0x0e100f00, 0x0c100a00, VFPv2 | VFPv3 | VFPv4, eEncodingA2, No_VFP, eSize32, self.decode_vldm),
        (0xffb00f10, 0xf2000110, AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vand_register),
        (0x0e100f00, 0x0c000b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vstm),
        (0x0e100f00, 0x0c000a00, VFPv2 | VFPv3 | VFPv4, eEncodingA2, No_VFP, eSize32, self.decode_vstm),
        (0x0ff003f0, 0x06e00070, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_uxtab),
        (0x0ff003f0, 0x06a00070, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_sxtab),
        (0xffb30f90, 0xf3b20000, AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vswp),
        (0x0ff003f0, 0x06f00070, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_uxtah),
        (0x0ff003f0, 0x06b00070, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_sxtah),
        (0x0fff0ff0, 0x06ff0f30, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_rbit),
        (0xfeb800b0, 0xf2800030, AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vmvn_immediate),
        (0xffb30f90, 0xf3b00580, AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vmvn_register),
        (0x0fe00030, 0x06a00010, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ssat),
        (0x0e100000, 0x0c000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_stc),
        (0xfe100000, 0xfc000000, ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_stc),
        (0x0fff0fff, 0x0ef10a10, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vmrs),
        (0x0f300f00, 0x0d000b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vstr),
        (0x0f300f00, 0x0d000a00, VFPv2 | VFPv3 | VFPv4, eEncodingA2, No_VFP, eSize32, self.decode_vstr),
        (0x0f300f00, 0x0d100b00, VFPv2 | VFPv3 | VFPv4 | AdvancedSIMD, eEncodingA1, No_VFP, eSize32, self.decode_vldr),
        (0x0f300f00, 0x0d100a00, VFPv2 | VFPv3 | VFPv4, eEncodingA2, No_VFP, eSize32, self.decode_vldr),
        (0x0fe0007f, 0x07c0001f, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_bfc),
        (0x0fe00070, 0x07c00010, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_bfi),
        (0x0f000010, 0x0e000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_cdp),
        (0xff000010, 0xfe000000, ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_cdp),
        (0xffffffff, 0xf57ff01f, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_clrex),
        (0xfff1fe20, 0xf1000000, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_cps),
        (0xfffffff0, 0xf57ff050, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_dmb),
        (0xfffffff0, 0xf57ff040, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_dsb),
        (0x0fffffff, 0x0160006e, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_eret),
        (0x0ff000f0, 0x01400070, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_hvc),
        (0xfffffff0, 0xf57ff060, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_isb),
        (0x0e100000, 0x0c100000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldc_immediate),
        (0xfffffff0, 0xfc100000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_ldc_immediate),
        (0x0e1f0000, 0x0c1f0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldc_literal),
        (0xfe1f0000, 0xfc1f0000, ARMv5TAll | ARMv6All | ARMv7 , eEncodingA2, No_VFP, eSize32, self.decode_ldc_literal),
        (0x0e5000f0, 0x004000d0, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrd_immediate),
        (0x0f7f00f0, 0x014f00d0, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrd_literal),
        (0x0e500ff0, 0x000000d0, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrd_register),
        (0x0f7f00f0, 0x015f00b0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrh_literal),
        (0x0f7000f0, 0x007000b0, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrht),
        (0x0f700ff0, 0x003000b0, ARMv6T2 | ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_ldrht),
        (0x0e5000f0, 0x005000d0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrsb_immediate),
        (0x0e5f00f0, 0x005f00d0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrsb_literal),
        (0x0e5000f0, 0x001000d0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrsb_register),
        (0x0f7000f0, 0x007000d0, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrsbt),
        (0x0f700ff0, 0x003000d0, ARMv6T2 | ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_ldrsbt),
        (0x0e5000f0, 0x005000f0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrsh_immediate),
        (0x0e5f00f0, 0x005f00f0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrsh_literal),
        (0x0e5000f0, 0x001000f0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrsh_register),
        (0x0f7000f0, 0x007000f0, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrsht),
        (0x0f700ff0, 0x003000f0, ARMv6T2 | ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_ldrsht),
         
        # VMOV (between two ARM core registers and a doubleword extension register)
        (0x0fe00fd0, 0x0c400b10, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_vmov_between_two_arm_core_registers_and_a_double_word_extension_register),
         
        # VMOV (between two ARM core registers and two single-precision registers)
        (0x0fe00fd0, 0x0c400a10, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_vmov_between_two_arm_core_registers_and_two_single_precision_registers),
         
        # VMOV (between ARM core register and single-precision register) 
        (0x0fe00f7f, 0x0e000a10, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_vmov_between_arm_core_register_and_single_precision_register),
         
        # VMOV (scalar to ARM core register)
        (0x0f100f1f, 0x0e100b10, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_vmov_scalar_to_arm_core_register),
         
        # VMOV (ARM core register to scalar)
        (0x0f900f1f, 0x0e000b10, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_vmov_arm_core_register_to_scalar),
         
        # VMOV register Advanced SIMD
        (0xffb00f10, 0xf2200110, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_vmov_register),

        # VMOV register Advanced SIMD
        (0x0fbf0ed0, 0x0eb00a40, ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_vmov_register),
         
        # VMOV Advanced SIMD
        (0xfeb80090, 0xf2800010, ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_vmov_immediate),

        # VMOV Advanced SIMD
        (0x0fb00ef0, 0x0eb00a00, ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_vmov_immediate),

        # CPS ARMv6*, ARMv7
        (0xfff1fe20, 0xf1000000, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_cps),
         
        # CLREX ARMv7
        (0xffffffff, 0xf57ff01f, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_clrex),
         
        # PLD, PLDW (immediate) 
        (0xff30f000, 0xf510f000, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_pld),
         
        # LDRH (register, ARM) ARMv4*, ARMv5T*, ARMv6*, ARMv7
        (0x0e500ff0, 0x001000b0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrh_register_arm),
         
        # LDRH (literal, ARM) ARMv4*, ARMv5T*, ARMv6*, ARMv7
        (0x0f7f00f0, 0x015f00b0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ldrh_literal_arm),
         
        # LDRH (immediate, ARM) ARMv4*, ARMv5T*, ARMv6*, ARMv7
        (0x0e5000f0, 0x005000b0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrh_immediate_arm),

        # ADC (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x02a00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_adc_immediate),
        
        # ADC (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x00a00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_adc_register),
        
        # ADC (register-shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x00a00010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_adc_rsr),
        
        # ADD (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x02800000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_add_immediate_arm),
        
        # ADD (register, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x00800000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_add_register_arm),
        
        # ADD (register-shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x00800010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_add_rsr),
        
        # ADR ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fff0000, 0x028f0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_adr),
        
        # ADR ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fff0000, 0x024f0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_adr),
        
        # AND (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x02000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_and_immediate),
        
        # AND (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x00000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_and_register),
        
        # AND (register-shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x00000010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_and_rsr),

        # ASR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0070, 0x01a00040, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_asr_immediate),
        
        # ASR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef00f0, 0x01a00050, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_asr_register),

        # BIC (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x03c00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_bic_immediate),
        
        # BIC (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x01c00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_bic_register),

        # BIC (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x01c00010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_bic_rsr),

        # BKPT ARMv5TAll | ARMv6All | ARMv7
        (0x0ff000f0, 0x01200070, ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_bkpt),

        # eEncodingA2 must be placed before eEncodingA1
        # BL, BLX (immediate) ARMv5TAll | ARMv6All | ARMv7
        (0xfe000000, 0xfa000000, ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_bl_immediate),
        
        # BL, BLX (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f000000, 0x0b000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_bl_immediate),

        # B ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f000000, 0x0a000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_b),

        # BLX (Register) ARMv5TAll | ARMv6All | ARMv7
        (0x0ffffff0, 0x012fff30, ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_blx_register),
        
        # BX ARMv4T | ARMv5TAll | ARMv6All | ARMv7
        (0x0ffffff0, 0x012fff10, ARMv4T | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_bx),
        
        # BXJ ARMv5TEJ, ARMv6All | ARMv7
        (0x0ffffff0, 0x012fff20, ARMv5TEJ | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_bxj),
             
        # CLZ ARMv5TAll | ARMv6All | ARMv7
        (0x0fff0ff0, 0x016f0f10, ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_clz),

        # CMN (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f000, 0x03700000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_cmn_immediate),

        # CMN (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f010, 0x01700000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_cmn_register),

        # CMN (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f090, 0x01700010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_cmn_rsr),
    
        # CMP (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f000, 0x03500000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_cmp_immediate),
        
        # CMP (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f010, 0x01500000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_cmp_register),

        # CMP (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f090, 0x01500010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_cmp_rsr),

        # DBG ARMv7 (executes as NOP in ARMv6Kand ARMv6T2)
        (0x0ffffff0, 0x0320f0f0, ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_dbg),
                
        # EOR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x02200000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_eor_immediate),
        
        # EOR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x00200000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_eor_register),

        # EOR (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x00200010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_eor_rsr),

        # RFE ARMv6All | ARMv7
        (0xfe50ffff, 0xf8100a00, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_rfe),

        # LDM/LDMIA/LDMFD (ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fd00000, 0x08900000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldmia_arm),
        
        # LDMDA/LDMFA ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fd00000, 0x08100000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldmda),
        
        # LDMDB/LDMEA ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fd00000, 0x09100000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldmdb),
        
        # LDMIB/LDMED ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fd00000, 0x09900000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldmib),
        
        # LDR (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e500000, 0x04100000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldr_immediate_arm),
        
        # LDR (literal) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f7f0000, 0x028f8000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldr_literal),
        
        # LDR (register, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e500010, 0x06100000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldr_register_arm),
        
        # LDRB (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e500000, 0x04500000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrb_immediate_arm),
        
        # LDRB (literal) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e5f0000, 0x045f0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrb_literal),
        
        # LDRB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0xfe500010, 0x06500000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrb_register),
        
        # LDRBT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f700000, 0x04700000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrbt),
        
        # LDRBT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f700010, 0x06700000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_ldrbt),
        
        # LDREX ARMv6All | ARMv7
        (0x0ff00fff, 0x01900f9f, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrex),
        
        # LDREXB ARMv6K | ARMv7
        (0x0ff00fff, 0x01d00f9f, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrexb),
        
        # LDREXD ARMv6K | ARMv7
        (0x0ff00fff, 0x01b00f9f, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrexd),
        
        # LDREXH ARMv6K | ARMv7
        (0x0ff00fff, 0x01f00f9f, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrexh),
        
        # LDRT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f700000, 0x04300000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ldrt),
        
        # LDRT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f700010, 0x06300000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_ldrt),
                
        # LSL (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0070, 0x01a00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_lsl_immediate),

        # LSL (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef00f0, 0x01a00010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_lsl_register),

        # LSR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0070, 0x01a00020, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_lsr_immediate),

        # LSR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef00f0, 0x01a00030, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_lsr_register),
        
        # MLA ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe000f0, 0x00200090, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_mla),

        # MLS ARMv6T2 | ARMv7
        (0x0ff000f0, 0x00600090, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_mls),

        # MOV (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0000, 0x03a00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_mov_immediate),
        
        # MOV (immediate) ARMv6T2 | ARMv7
        (0x0ff00000, 0x03000000, ARMv6T2 | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_mov_immediate),

        # MOV (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0ff0, 0x01a00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_mov_register_arm),
        
        # MOVT ARMv6T2 | ARMv7
        (0x0ff00000, 0x03400000, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_movt),

        # MUL ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe000f0, 0x00000090, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_mul),

        # MVN (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0000, 0x03e00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_mvn_immediate),
        
        # MVN (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0010, 0x01e00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_mvn_register),

        # MVN (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0090, 0x01e00010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_mvn_rsr),

        # NOP ARMv6K, ARMv6T2 | ARMv7
        (0x0fffffff, 0x0320f000, ARMv6K | ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_nop),

        # ORR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x03800000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_orr_immediate),

        # ORR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x01800000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_orr_register),

        # ORR (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x01800010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_orr_rsr),

        # POP ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fff0000, 0x08bd0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_pop_arm),
        
        # POP ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fff0fff, 0x049d0004, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_pop_arm),

        # PUSH ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fff0000, 0x092d0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_push),
        
        # PUSH ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fff0fff, 0x052d0004, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_push),

        # ROR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0070, 0x01a00060, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ror_immediate),

        # ROR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef00f0, 0x01a00070, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_ror_register),

        # RRX ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0ff0, 0x01a00060, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_rrx),

        # RSB (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x02600000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_rsb_immediate),

        # RSB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x00600000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_rsb_register),
        
        # RSB (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x00600010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_rsb_rsr),
                
        # RSC (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x02e00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_rsc_immediate),
        
        # RSC (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x00e00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_rsc_register),

        # RSC (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x00e00010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_rsc_rsr),
        
        # SBC (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x02c00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sbc_immediate),
        
        # SBC (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x00c00000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sbc_register),

        # SBC (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x00c00010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sbc_rsr),

        # SEV ARMv6K | ARMv7 (executes as NOP in ARMv6T2)
        (0x0fffffff, 0x0320f004, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sev),
        
        # SMLABB, SMLABT, SMLATB, SMLATT ARMv5TEAll | ARMv6All | ARMv7
        (0x0ff00090, 0x01000080, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_smla),
        
        # SMLALBB, SMLALBT, SMLALTB, SMLALTT ARMv5TEAll | ARMv6All | ARMv7
        (0x0ff00090, 0x01400080, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_smlal),
        
        # SMLAWB, SMLAWT ARMv5TEAll | ARMv6All | ARMv7
        (0x0ff000b0, 0x01200080, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_smlaw),

        # SMULBB, SMULBT, SMULTB, SMULTT ARMv5TEAll | ARMv6All | ARMv7
        (0x0ff0f090, 0x01600080, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_smul),
        
        # SMULL ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe000f0, 0x00c00090, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_smull),
        
        # SMULWB ARMv5TEAll | ARMv6All | ARMv7
        (0x0ff0f0b0, 0x012000a0, ARMv5TEAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_smulw),
        
        # SRS ARMv6All | ARMv7
        (0xfe5fffe0, 0xf84d0500, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_srs_arm),

        # STM (STMIA, STMEA) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fd00000, 0x08800000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_stmia),
        
        # STMDA (STMED) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fd00000, 0x08000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_stmda),
        
        # STMDB (STMFD) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fd00000, 0x09000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_stmdb),
        
        # STMIB (STMFA) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fd00000, 0x09800000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_stmib),
        
        # STR (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e500000, 0x04000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_str_immediate_arm),

        # STR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e500010, 0x06000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_str_reg),
        
        # STRH (immediate, ARM) ARMv4*, ARMv5T*, ARMv6*, ARMv7
        (0x0e5000f0, 0x004000b0, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_strh_immediate_arm),
        
        # STRB (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e500000, 0x04400000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_strb_immediate_arm),
        
        # STRB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e500010, 0x06400000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_strb_register),

        # STRBT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f700000, 0x04600000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_strbt),

        # STRBT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f700010, 0x06600000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_strbt),

        # STREX ARMv6All | ARMv7
        (0x0ff00ff0, 0x01800f90, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_strex),

        # STREXB ARMv6K | ARMv7
        (0x0ff00ff0, 0x01c00f90, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_strexb),

        # STREXD ARMv6K | ARMv7
        (0x0ff00ff0, 0x01a00f90, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_strexd),

        # STREXH ARMv6K | ARMv7
        (0x0ff00ff0, 0x01e00f90, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_strexh),

        # STRT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f700000, 0x04200000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_strt),
        
        # STRT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f700010, 0x06200000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_strt),
                
        # SUB (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00000, 0x02400000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sub_immediate_arm),

        # SUB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00010, 0x00400000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sub_register),

        # SUB (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe00090, 0x00400010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sub_rsr),
        
        # SUB (SP minus immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0000, 0x024d0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sub_sp_minus_immediate),

        # SUB (SP minus register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fef0010, 0x004d0000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_sub_sp_minus_register),

        # SUBS PC, LR and related instructions, ARM ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e10f000, 0x0210f000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_subs_pc_lr_arm),
        
        # SUBS PC, LR and related instructions, ARM ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0e10f010, 0x0010f000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32 , self.decode_subs_pc_lr_arm),
        
        # SVC ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0f000000, 0x0f000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_svc),
        
        # SWP, SWPB ARMv4All | ARMv5TAll | deprecated in ARMv6All and ARMv7, optional in ARMv7VE
        (0x0fb00ff0, 0x01000090, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_swp),
        
        # TEQ (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f000, 0x03300000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_teq_immediate),
        
        # TEQ (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f010, 0x01300000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_teq_register),
        
        # TEQ (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f090, 0x01300010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_teq_rsr),
         
        # TST (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f000, 0x03100000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_tst_immediate),
        
        # TST (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f010, 0x01100000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_tst_register),

        # TST (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0ff0f090, 0x01100010, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_tst_rsr),

        # UMAAL ARMv6All | ARMv7
        (0x0ff000f0, 0x00400090, ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_umaal),
        
        # UMLAL ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe000f0, 0x00a00090, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_umlal),
        
        # UMULL ARMv4All | ARMv5TAll | ARMv6All | ARMv7
        (0x0fe000f0, 0x00800090, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32 , self.decode_umull),
        
        (0x0fffffff, 0x0320f001, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_yield),
        (0x0fffffff, 0x0320f002, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_wfe),
        (0x0fffffff, 0x0320f003, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_wfi),
        (0x0fffffff, 0x0320f004, ARMv6K | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_sev),
        
        # UBFX ARMv6T2, ARMv7
        (0x0fe00070, 0x07e00050, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_ubfx),

        # UXTB ARMv6T2, ARMv7
        (0x0fff03f0, 0x06ef0070, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_uxtb),

        # MRC ARMv4*, ARMv5T*, ARMv6*, ARMv7
        (0x0f100010, 0x0e100010, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_mrc),

        # MRC ARMv5T*, ARMv6*, ARMv7
        (0xff100010, 0xfe100010, ARMv6T2 | ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_mrc),

        # BFC ARMv6T2, ARMv7
        (0x0fe0007f, 0x07c0001f, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_bfc),

        # BFI ARMv6T2, ARMv7
        (0x0fe00070, 0x07c00010, ARMv6T2 | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_bfi),
        
        # CDP ARMv4*, ARMv5T*, ARMv6*, ARMv7
        (0x0f000010, 0x0e000000, ARMv4All | ARMv5TAll | ARMv6All | ARMv7, eEncodingA1, No_VFP, eSize32, self.decode_cdp),

        # CDP ARMv5T*, ARMv6*, ARMv7
        (0xff000010, 0xfe000000, ARMv5TAll | ARMv6All | ARMv7, eEncodingA2, No_VFP, eSize32, self.decode_cdp),
        
        (0x00000000, 0x00000000, ARMvAll, eEncodingA1, No_VFP, eSize32, self.decode_unknown)
    )
    
    def decode_arm(self, opcode):        
        decoder_entry = None
        for e in self.arm_table:
            if (opcode & e[0] == e[1]) and (self.arm_isa & e[2]):
                decoder_entry = e
                break
        
        ins = None    
        if decoder_entry:
            # Instruction encoding
            encoding = decoder_entry[3]
            
            # Instruction decoder function
            decode = decoder_entry[6]
            
            ins = decode(opcode, encoding)

        return ins

    def __is_thumb32__(self, opcode):
        """
        A6.1 Thumb instruction set encoding
        If the value of bits[15:11] of the halfword being decoded is one of the following,
        the halfword is the first halfword of a 32-bit instruction:

            0b11101
            0b11110
            0b11111
        """
        return get_bits(opcode & 0x0000ffff, 15, 11) in [0b11101, 0b11110, 0b11111]

    def decode_thumb(self, opcode):
        is_thumb32 = False

        # If the instruction is THUMB32 then we need to change the order.
        if self.__is_thumb32__(opcode):
            is_thumb32 = True
            opcode = ((opcode & 0xffff0000) >> 16) | ((opcode & 0x0000ffff) << 16)

        elif opcode == 0xf3bf8f2f:
            # Special case for CLREX
            pass

        else:
            opcode &= 0x0000ffff

        decoder_entry = None
        for e in self.thumb_table:
            if (opcode & e[0] == e[1]) and (self.arm_isa & e[2]):
                decoder_entry = e
                break
        
        ins = None
        if decoder_entry:
            # Instruction encoding
            encoding = decoder_entry[3]
            
            # Instruction decoder function
            decode = decoder_entry[6]
            
            ins = decode(opcode, encoding)

        ins.thumb32 = is_thumb32

        return ins
     
    def disassemble_buffer(self, ins_stream, mode=ARMMode.ARM):
        """
        Disassemble a stream of instructions in string form.
        Return a list of all the disassembled instructions.
        So far we do not take into account changes of processor mode. We will have to decide what we do 
        in those cases.
        """
        import struct
        ret = []
        
        if mode == ARMMode.ARM:
            opcodes = struct.unpack("<" + ("L" * (len(ins_stream) / 4)), ins_stream)           
            for opcode in opcodes:
                ins = self.decode_arm(opcode)
                ret.append(ins)
        
        else:
            opcodes = struct.unpack("<" + ("H" * (len(ins_stream) / 2)), ins_stream)
            for opcode in opcodes:
                print "%.4x" %opcode
                ins = self.decode_thumb(opcode)
                ret.append(ins)
                
        return ret
    
    def disassemble(self, opcode, mode=ARMMode.ARM):
        """
        """
        if (opcode, mode) in self.cache:
            return self.cache[(opcode, mode)]
        
        if mode == ARMMode.THUMB:
            ins = self.decode_thumb(opcode)
        
        else:
            ins = self.decode_arm(opcode)
        
        self.cache[(opcode, mode)] = ins
        
        return ins
    
    def ArchVersion(self):
        return self.arm_isa

    def CountITSize(self, ITMask):
        """
        Number of conditional instructions.
        """
        TZ = CountTrailingZeros(ITMask)
        return 4 - TZ

    def InitIT(self, ITState):
        """
        Init ITState.
        """
        self.ITCounter = self.CountITSize(ITState & 0b1111)
        self.ITState = ITState

    def ITAdvance(self):
        """
        Update ITState if necessary.
        """
        self.ITCounter -= 1
        
        if self.ITCounter == 0:
            self.ITState = 0
        else:
            NewITState4_0 = (self.ITState & 0b11111) << 1
            self.ITState = (self.ITState & 0b11100000) | NewITState4_0

    def LastInITBlock(self):
        """
        Return true if we're the last instruction inside an IT Block.
        """
        return self.ITCounter == 1

    def InITBlock(self):
        """
        Return true if we're inside an IT Block.
        """
        return self.ITCounter != 0

    def decode_condition_field(self, opcode):
        """
        Every conditional opcode contains a 4-bit condition code field, the cond field, in bits 31 to 28
        """
        condition_code = (opcode & (0b1111 << 28)) >> 28
        return Condition(condition_code)

    def decode_srs_thumb(self, opcode, encoding):
        """
        B9.3.15 SRS, Thumb
        Store Return State stores the LR and SPSR of the current mode to the stack of a specified mode.         
        """
        props = {}
        ins_id = ARMInstruction.srs
        if encoding == eEncodingT1:
            W = get_bit(opcode, 21)
            mode = get_bits(opcode, 4, 0)
            
            # if CurrentInstrSet() == InstrSet_ThumbEE then UNPREDICTABLE;
            wback = W == 1
            increment = False
            wordhigher = False

            operands = [Register(ARMRegister.SP.reg, wback), Immediate(mode)]
            ins = Instruction(ins_id, opcode, "SRSDB", False, None, operands, encoding)
        
        elif encoding == eEncodingT2:
            W = get_bit(opcode, 21)
            mode = get_bits(opcode, 4, 0)
            
            # if CurrentInstrSet() == InstrSet_ThumbEE then UNPREDICTABLE;
            wback = W == 1
            increment = True
            wordhigher = False

            operands = [Register(ARMRegister.SP.reg, wback), Immediate(mode)]
            ins = Instruction(ins_id, opcode, "SRSIA", False, None, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins
    
    def decode_srs_arm(self, opcode, encoding):
        """
        B9.3.16 SRS, ARM
        Store Return State stores the LR and SPSR of the current mode to the stack of a specified mode. 
        
        Syntax:
        SRS{<amode>}{<c>}{<q>} SP{!}, #<mode>
        """
        props = {}
        ins_id = ARMInstruction.srs
        condition = self.decode_condition_field(opcode)
        
        P = get_bit(opcode, 24)
        U = get_bit(opcode, 23)
        W = get_bit(opcode, 21)
        mode = get_bits(opcode, 4, 0)
        
        wback = W == 1
        inc = U == 1
        wordhigher = P == U

        if P == 0 and U == 0:
            # Decrement After.
            operands = [Register(ARMRegister.SP.reg, wback), Immediate(mode)]
            ins = Instruction(ins_id, opcode, "SRSDA", False, condition, operands, encoding)
        
        elif P == 1 and U == 0:
            # Decrement Before.
            operands = [Register(ARMRegister.SP.reg, wback), Immediate(mode)]
            ins = Instruction(ins_id, opcode, "SRSDB", False, condition, operands, encoding)
        
        elif P == 0 and U == 1:
            # Increment After. 
            operands = [Register(ARMRegister.SP.reg, wback), Immediate(mode)]
            ins = Instruction(ins_id, opcode, "SRSIA", False, condition, operands, encoding)
        
        elif P == 1 and U == 1:
            # Increment Before.
            operands = [Register(ARMRegister.SP.reg, wback), Immediate(mode)]
            ins = Instruction(ins_id, opcode, "SRSIB", False, condition, operands, encoding)
        
        return ins
    
    def decode_rfe(self, opcode, encoding):
        """
        B9.3.13 RFE
        Return From Exception loads the PC and the CPSR from the word at the specified address and the following word
        respectively.
        
        Syntax:
        RFE{<amode>}{<c>}{<q>} <Rn>{!}
        """
        props = {}
        ins_id = ARMInstruction.rfe
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            wback = W == 1
            increment = False
            wordhigher = False

            # if CurrentInstrSet() == InstrSet_ThumbEE then UNPREDICTABLE;
            
            # if n == 15 then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()
            
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rn, wback)]
            ins = Instruction(ins_id, opcode, "RFEDB", False, condition, operands, encoding)
        
        elif encoding == eEncodingT2:
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            wback = W == 1
            increment = True
            wordhigher = False
            
            # if CurrentInstrSet() == InstrSet_ThumbEE then UNPREDICTABLE;
            
            # if n == 15 then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()
            
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            # NOTE: IA mode is not clear from the documentation. Verify this.
            condition = None
            operands = [Register(Rn, wback)]
            ins = Instruction(ins_id, opcode, "RFEIA", False, condition, operands, encoding)
        
        elif encoding == eEncodingA1:
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            
            # if CurrentInstrSet() == InstrSet_ThumbEE then UNPREDICTABLE;
            wback = W == 1
            increment = U == 1
            wordhigher = P == U
                        
            # if n == 15 then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()
            
            operands = [Register(Rn, wback)]
        
            if P == 0 and U == 0: 
                ins = Instruction(ins_id, opcode, "RFEDA", False, None, operands, encoding)
            
            elif P == 1 and U == 0:
                ins = Instruction(ins_id, opcode, "RFEDB", False, None, operands, encoding)
            
            elif P == 0 and U == 1:
                ins = Instruction(ins_id, opcode, "RFEIA", False, None, operands, encoding)
            
            elif P == 1 and U == 1:
                ins = Instruction(ins_id, opcode, "RFEIB", False, None, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                    
        return ins
            
    def decode_mrc(self, opcode, encoding):
        """
        A8.8.107
        MRC, MRC2
        Move to ARM core register from Coprocessor causes a coprocessor to transfer a value to an ARM core register or
        to the condition flags. If no coprocessor can execute the instruction, an Undefined Instruction exception is
        generated.        
        """
        props = {}
        ins_id = ARMInstruction.mrc
        
        condition = self.decode_condition_field(opcode) if encoding == eEncodingA1 else None              
            
        opc1 = get_bits(opcode, 23, 21)
        CRn = get_bits(opcode, 19, 16)
        Rt = get_bits(opcode, 15, 12)
        coproc = get_bits(opcode, 11, 8)
        opc2 = get_bits(opcode, 7, 5)
        CRm = get_bits(opcode, 3, 0)
        
        # if coproc IN "101x" then SEE "Advanced SIMD and Floating-point";
        if coproc in [0b1010, 0b1011] and encoding in [eEncodingT1, eEncodingA1]:
            raise RuntimeError("SEE Advanced SIMD and Floating-point")
        
        elif coproc in [0b1010, 0b1011]:
            raise UnpredictableInstructionException()
        
        # if t == 13 && (CurrentInstrSet() != InstrSet_ARM) then UNPREDICTABLE;
        if Rt == 13 and encoding == eEncodingA1:
            raise UnpredictableInstructionException()
            
        # MRC{2}{<c>}{<q>} <coproc>, {#}<opc1>, <Rt>, <CRn>, <CRm>{, {#}<opc2>}
        # 2: If specified, selects encoding T2/A2. If omitted, selects encoding T1/A1.
        # <coproc> The name of the coprocessor. The generic coprocessor names are p0-p15.
        # <opc1> Is a coprocessor-specific opcode in the range 0 to 7.
        # <Rt> Is the destination ARM core register. This register can be R0-R14 or APSR_nzcv.
        # <CRn> Is the coprocessor register that contains the first operand.
        # <CRm> Is an additional source or destination coprocessor register.
        # <opc2> Is a coprocessor-specific opcode in the range 0 to 7. If omitted, <opc2> is assumed to be 0.
        
        name = "MRC" if not encoding in [eEncodingA2, eEncodingT2] else "MRC2"
        operands = [CoprocessorName(coproc), CoprocessorOpCode(opc1), Register(Rt),
                    CoprocessorRegister(CRn), CoprocessorRegister(CRm), CoprocessorOpCode(opc2)]
        
        ins = Instruction(ins_id, opcode, name, False, condition, operands, encoding)
        return ins
        
    def decode_swp(self, opcode, encoding):
        """
        A8.8.229
        SWP, SWPB
        SWP (Swap) swaps a word between registers and memory. SWP loads a word from the memory address given by the
        value of register <Rn>. The value of register <Rt2> is then stored to the memory address given by the value of <Rn>,
        and the original loaded value is written to register <Rt>. If the same register is specified for <Rt> and <Rt2>, this
        instruction swaps the value of the register and the value at the memory address.
        
        Syntax:
        SWP{B}{<c>}{<q>} <Rt>, <Rt2>, [<Rn>]
        """
        props = {}
        ins_id = ARMInstruction.swp
        condition = self.decode_condition_field(opcode)
                
        if encoding == eEncodingA1:
            B = get_bit(opcode, 22)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rt2 = get_bits(opcode, 3, 0)
                        
            # if t == 15 || t2 == 15 || n == 15 || n == t || n == t2 then UNPREDICTABLE;
            if Rt == 15 or Rt2 == 15 or Rn == 15 or Rn == Rt or Rn == Rt2:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rt), Register(Rt2), Memory(Register(Rn))]
        
        name = "SWPB" if B == 1 else "SWP"
        ins = Instruction(ins_id, opcode, name, False, condition, operands, encoding)

        return ins
    
    def decode_strex(self, opcode, encoding):
        """
        A8.8.212
        STREX
        Store Register Exclusive calculates an address from a base register value and an immediate offset, and stores a word
        from a register to memory if the executing processor has exclusive access to the memory addressed.  
        
        Syntax:
        STREX{<c>}{<q>} <Rd>, <Rt>, [<Rn> {, #<imm>}]
        """
        props = {}
        ins_id = ARMInstruction.strex
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rd = get_bits(opcode, 11, 8)
            imm8 = get_bits(opcode, 7, 0)

            # if d IN {13,15} || t IN {13,15} || n == 15 then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rt) or Rn == 15:
                raise UnpredictableInstructionException()
            
            # if d == n || d == t then UNPREDICTABLE;
            if Rd == Rn or Rd == Rt:
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rt), Memory(Register(Rn), Immediate(imm8))]
            ins = Instruction(ins_id, opcode, "STREX", False, condition, operands, encoding)

        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 15, 12)
            Rt = get_bits(opcode, 3, 0)
            imm8 = 0

            # if d == 15 || t == 15 || n == 15 then UNPREDICTABLE;
            if Rd == 15 or Rt == 15 or Rn == 15:
                raise UnpredictableInstructionException()
            
            # if d == n || d == t then UNPREDICTABLE;
            if Rd == Rn or Rd == Rt:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rt), Memory(Register(Rn))]
            ins = Instruction(ins_id, opcode, "STREX", False, condition, operands, encoding)            

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_ldrex(self, opcode, encoding):
        """
        A8.8.75
        LDREX
        Load Register Exclusive calculates an address from a base register value and an immediate offset, loads a word from
        memory, writes it to a register and:
        
          - if the address has the Shared Memory attribute, marks the physical address as exclusive access for the
            executing processor in a global monitor
            
          - causes the executing processor to indicate an active exclusive access in the local monitor.        
          
        Syntax:
        LDREX{<c>}{<q>} <Rt>, [<Rn> {, #<imm>}]
        """
        props = {}
        ins_id = ARMInstruction.ldrex
        condition = self.decode_condition_field(opcode)

        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm8 = get_bits(opcode, 7, 0)

            # if t IN {13,15} || n == 15 then UNPREDICTABLE;
            if BadReg(Rt) or Rn == 15:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm8 = 0

            # if t == 15 || n == 15 then UNPREDICTABLE;
            if Rt == 15 or Rn == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rt), Memory(Register(Rn), Immediate(imm8))]
        ins = Instruction(ins_id, opcode, "LDREX", False, condition, operands, encoding)
        return ins

    def decode_strexd(self, opcode, encoding):
        """
        A8.8.214
        STREXD
        Store Register Exclusive Doubleword derives an address from a base register value, and stores a 64-bit doubleword
        from two registers to memory if the executing processor has exclusive access to the memory addressed.        
        
        Syntax:
        STREXD{<c>}{<q>} <Rd>, <Rt>, <Rt2>, [<Rn>]
        """
        props = {}
        ins_id = ARMInstruction.strexd
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rt2 = get_bits(opcode, 11, 8)
            Rd = get_bits(opcode, 3, 0)

            # if d IN {13,15} || t IN {13,15} || t2 IN {13,15} || n == 15 then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rt) or BadReg(Rt2) or Rn == 15:
                raise UnpredictableInstructionException()
            
            # if d == n || d == t || d == t2 then UNPREDICTABLE;
            if Rd == Rn or Rd == Rt or Rd == Rt2:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 15, 12)
            Rt = get_bits(opcode, 3, 0)
            Rt2 = Rt + 1

            # if d == 15 || Rt<0> == '1' || Rt == '1110' || n == 15 then UNPREDICTABLE;
            if Rd == 15 or get_bit(Rt, 0) == 1 or Rt == 0b1110 or Rn == 15:
                raise UnpredictableInstructionException()
            
            # if d == n || d == t || d == t2 then UNPREDICTABLE;
            if Rd == Rn or Rd == Rt or Rd == Rt2:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rt), Register(Rt2), Memory(Register(Rn))]
        ins = Instruction(ins_id, opcode, "STREXD", False, condition, operands, encoding)
        return ins

    def decode_ldrexd(self, opcode, encoding):
        """
        A8.8.77
        LDREXD
        Load Register Exclusive Doubleword derives an address from a base register value, loads a 64-bit doubleword from
        memory, writes it to two registers and:
        - if the address has the Shared Memory attribute, marks the physical address as exclusive access for the
           executing processor in a global monitor
        - causes the executing processor to indicate an active exclusive access in the local monitor.        
        
        Syntax:
        LDREXD{<c>}{<q>} <Rt>, <Rt2>, [<Rn>]
        """
        props = {}
        ins_id = ARMInstruction.ldrexd
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rt2 = get_bits(opcode, 11, 8)

            # if t IN {13,15} || t2 IN {13,15} || t == t2 || n == 15 then UNPREDICTABLE;
            if BadReg(Rt) or BadReg(Rt2) or Rt == Rt2 or Rn == 15:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rt2 = Rt + 1

            # if Rt<0> == '1' || Rt == '1110' || n == 15 then UNPREDICTABLE;
            if get_bit(Rt, 0) == 1 or Rt == 0b1110 or Rn == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rt), Register(Rt2), Memory(Register(Rn))]
        ins = Instruction(ins_id, opcode, "LDREXD", False, condition, operands, encoding)
        return ins

    def decode_strexb(self, opcode, encoding):
        """
        A8.8.213
        STREXB
        Store Register Exclusive Byte derives an address from a base register value, and stores a byte from a register to
        memory if the executing processor has exclusive access to the memory addressed.        
        
        Syntax:
        STREXB{<c>}{<q>} <Rd>, <Rt>, [<Rn>]
        """
        props = {}
        ins_id = ARMInstruction.strexb
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rd = get_bits(opcode, 3, 0)

            # if d IN {13,15} || t IN {13,15} || n == 15 then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rt) or Rn == 15:
                raise UnpredictableInstructionException()
            
            # if d == n || d == t then UNPREDICTABLE;
            if Rd == Rn or Rd == Rt:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 15, 12)
            Rt = get_bits(opcode, 3, 0)

            # if d == 15 || t == 15 || n == 15 then UNPREDICTABLE;
            if Rd == 15 or Rt == 15 or Rn == 15:
                raise UnpredictableInstructionException()
            
            # if d == n || d == t then UNPREDICTABLE;
            if Rd == Rn or Rd == Rt:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rt), Memory(Register(Rn))]
        ins = Instruction(ins_id, opcode, "STREXB", False, condition, operands, encoding)
        return ins

    def decode_ldrexb(self, opcode, encoding):
        """
        A8.8.76
        LDREXB
        Load Register Exclusive Byte derives an address from a base register value, loads a byte from memory, zero-extends
        it to form a 32-bit word, writes it to a register and:
        - if the address has the Shared Memory attribute, marks the physical address as exclusive access for the
           executing processor in a global monitor
        - causes the executing processor to indicate an active exclusive access in the local monitor.        
        
        Syntax:
        LDREXB{<c>}{<q>} <Rt>, [<Rn>]
        """
        props = {}
        ins_id = ARMInstruction.ldrexb
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)

            # if t IN {13,15} || n == 15 then UNPREDICTABLE;
            if BadReg(Rt) or Rn == 15:
                raise UnpredictableInstructionException()
                        
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)

            # if t == 15 || n == 15 then UNPREDICTABLE;
            if Rt == 15 or Rn == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rt), Memory(Register(Rn))]
        ins = Instruction(ins_id, opcode, "LDREXB", False, condition, operands, encoding)
        return ins

    def decode_strexh(self, opcode, encoding):
        """
        A8.8.215
        STREXH
        Store Register Exclusive Halfword derives an address from a base register value, and stores a halfword from a
        register to memory if the executing processor has exclusive access to the memory addressed.        

        Syntax:
        STREXH{<c>}{<q>} <Rd>, <Rt>, [<Rn>]
        """
        props = {}
        ins_id = ARMInstruction.strexh
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rd = get_bits(opcode, 3, 0)

            # if d IN {13,15} || t IN {13,15} || n == 15 then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rt) or Rn == 15:
                raise UnpredictableInstructionException()
            
            # if d == n || d == t then UNPREDICTABLE;s
            if Rd == Rn or Rd == Rt:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 15, 12)
            Rt = get_bits(opcode, 3, 0)

            # if d == 15 || t == 15 || n == 15 then UNPREDICTABLE;
            if Rd == 15 or Rt == 15 or Rn == 15:
                raise UnpredictableInstructionException()
            
            # if d == n || d == t then UNPREDICTABLE;
            if Rd == Rn or Rd == Rt:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
    
        operands = [Register(Rd), Register(Rt), Memory(Register(Rn))]
        ins = Instruction(ins_id, opcode, "STREXH", False, condition, operands, encoding)
        return ins
            
    def decode_ldrexh(self, opcode, encoding):
        """
        A8.8.78
        LDREXH
        Load Register Exclusive Halfword derives an address from a base register value, loads a halfword from memory,
        zero-extends it to form a 32-bit word, writes it to a register and:
        - if the address has the Shared Memory attribute, marks the physical address as exclusive access for the
           executing processor in a global monitor
        - causes the executing processor to indicate an active exclusive access in the local monitor.        
        
        Syntax:
        LDREXH{<c>}{<q>} <Rt>, [<Rn>]
        """
        props = {}
        ins_id = ARMInstruction.ldrexh
        condition = self.decode_condition_field(opcode)
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)

            # if t IN {13,15} || n == 15 then UNPREDICTABLE;
            if BadReg(Rt) or Rn == 15:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)

            # if t == 15 || n == 15 then UNPREDICTABLE;
            if Rt == 15 or Rn == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rt), Memory(Register(Rn))]
        ins = Instruction(ins_id, opcode, "LDREXH", False, condition, operands, encoding)
        return ins
        
    def decode_mul(self, opcode, encoding):
        """
        A8.8.114
        MUL
        Multiply multiplies two register values. The least significant 32 bits of the result are written to the destination
        register. These 32 bits do not depend on whether the source register values are considered to be signed values or
        unsigned values.
        
        Syntax:
        MUL{S}{<c>}{<q>} <Rd>, <Rn>{, <Rm>}
        """
        props = {}
        ins_id = ARMInstruction.mul
        condition = self.decode_condition_field(opcode)
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 5, 3)
            Rd = get_bits(opcode, 2, 0)
            Rm = Rd
        
            setflags = not self.InITBlock()
            
            # if ArchVersion() < 6 && d == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and Rd == Rn:
                raise UnpredictableInstructionException()
            
            condition = None
                    
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
        
            setflags = False
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
        
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)

            S = get_bit(opcode, 20)
            setflags = S == 1
            
            # if d == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            # if ArchVersion() < 6 && d == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and Rd == Rn:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Register(Rm)]
        ins = Instruction(ins_id, opcode, "MUL", setflags, condition, operands, encoding)        
        return ins

    def decode_mla(self, opcode, encoding):
        """
        A8.8.100
        MLA
        Multiply Accumulate multiplies two register values, and adds a third register value. The least significant 32 bits of
        the result are written to the destination register. These 32 bits do not depend on whether the source register values
        are considered to be signed values or unsigned values        
        
        Syntax:
        MLA{S}{<c>}{<q>} <Rd>, <Rn>, <Rm>, <Ra>
        """
        props = {}
        ins_id = ARMInstruction.mla
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Ra = get_bits(opcode, 15, 12)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
        
            setflags = False
            
            # if Ra == '1111' then SEE MUL;
            if Ra == 0b1111:
                return self.decode_mul(opcode, encoding)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} || a == 13 then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm) or Ra == 13:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 19, 16)
            Ra = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)

            S = get_bit(opcode, 20)
            setflags = S == 1
            
            # if d == 15 || n == 15 || m == 15 || a == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15 or Ra == 15:
                raise UnpredictableInstructionException()

            # if ArchVersion() < 6 && d == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and Rd == Rn:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rn), Register(Rm), Register(Ra)]
        ins = Instruction(ins_id, opcode, "MLA", setflags, condition, operands, encoding)
        return ins

    def decode_umaal(self, opcode, encoding):
        """
        A8.8.255
        UMAAL
        Unsigned Multiply Accumulate Accumulate Long multiplies two unsigned 32-bit values to produce a 64-bit value,
        adds two unsigned 32-bit values, and writes the 64-bit result to two registers.
        
        Syntax:
        UMAAL{<c>}{<q>} <RdLo>, <RdHi>, <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.umaal
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            RdHi = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            # if dLo IN {13,15} || dHi IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(RdLo) or BadReg(RdHi) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            RdHi = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)
           
            # if dLo == 15 || dHi == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if RdLo == 15 or RdHi == 15 or Rn == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        operands = [Register(RdLo), Register(RdHi), Register(Rn), Register(Rm)]
        ins = Instruction(ins_id, opcode, "UMAAL", False, condition, operands, encoding)
        return ins

    def decode_mls(self, opcode, encoding):
        """
        A8.8.101
        MLS
        Multiply and Subtract multiplies two register values, and subtracts the product from a third register value. The least
        significant 32 bits of the result are written to the destination register. These 32 bits do not depend on whether the
        source register values are considered to be signed values or unsigned values.
        
        Syntax:
        MLS{<c>}{<q>} <Rd>, <Rn>, <Rm>, <Ra>
        """
        props = {}
        ins_id = ARMInstruction.mls
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Ra = get_bits(opcode, 15, 12)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} || a IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm) or BadReg(Ra):
                raise UnpredictableInstructionException()
            
            condition = None
                
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 19, 16)
            Ra = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)
            
            # if d == 15 || n == 15 || m == 15 || a == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15 or Ra == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Register(Rm), Register(Ra)]
        ins = Instruction(ins_id, opcode, "MLS", False, condition, operands, encoding)
        return ins

    def decode_umull(self, opcode, encoding):
        """        
        A8.8.257
        UMULL
        Unsigned Multiply Long multiplies two 32-bit unsigned values to produce a 64-bit result.
        In ARM instructions, the condition flags can optionally be updated based on the result. Use of this option adversely
        affects performance on many processor implementations.
        
        Syntax:
        UMULL{S}{<c>}{<q>} <RdLo>, <RdHi>, <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.umull
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            RdHi = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            setflags = False
            
            # if dLo IN {13,15} || dHi IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(RdLo) or BadReg(RdHi) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            condition = None
                
        elif encoding == eEncodingA1:
            RdHi = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)
            
            S = get_bit(opcode, 20)
            setflags = S == 1
            
            # if dLo == 15 || dHi == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if RdLo == 15 or RdHi == 15 or Rn == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && (dHi == n || dLo == n) then UNPREDICTABLE;
            if self.ArchVersion() < 7 and ((RdHi == Rn) or (RdLo == Rn)):
                raise UnpredictableInstructionException() 

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(RdLo), Register(RdHi), Register(Rn), Register(Rm)]
        ins = Instruction(ins_id, opcode, "UMULL", setflags, condition, operands, encoding)
        return ins

    def decode_mull(self, opcode, encoding):
        ins_id = ARMInstruction.mull
        condition = self.decode_condition_field(opcode)
        raise InstructionNotImplementedException("decode_mull")

    def decode_umlal(self, opcode, encoding):
        """
        A8.8.256
        UMLAL
        Unsigned Multiply Accumulate Long multiplies two unsigned32-bit values to produce a 64-bit value, and
        accumulates this with a 64-bit value.   
        
        Syntax:
        UMLAL{S}{<c>}{<q>} <RdLo>, <RdHi>, <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.umlal
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            RdHi = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            setflags = False
            
            # if dLo IN {13,15} || dHi IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(RdLo) or BadReg(RdHi) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            condition = None
                
        elif encoding == eEncodingA1:
            RdHi = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)
            
            S = get_bit(opcode, 20)
            setflags = S == 1
            
            # if dLo == 15 || dHi == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if RdLo == 15 or RdHi == 15 or Rn == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && (dHi == n || dLo == n) then UNPREDICTABLE;
            if self.ArchVersion() < 7 and ((RdHi == Rn) or (RdLo == Rn)):
                raise UnpredictableInstructionException() 

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(RdLo), Register(RdHi), Register(Rn), Register(Rm)]
        ins = Instruction(ins_id, opcode, "UMLAL", setflags, condition, operands, encoding)
        return ins

    def decode_smull(self, opcode, encoding):
        """
        A8.8.189
        SMULL
        Signed Multiply Long multiplies two 32-bit signed values to produce a 64-bit result.        
        
        Syntax:
        SMULL{S}{<c>}{<q>} <RdLo>, <RdHi>, <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.smull
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            RdHi = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            setflags = False
            
            # if dLo IN {13,15} || dHi IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(RdLo) or BadReg(RdHi) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            condition = None
                
        elif encoding == eEncodingA1:
            RdHi = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)
            
            S = get_bit(opcode, 20)
            setflags = S == 1
            
            # if dLo == 15 || dHi == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if RdLo == 15 or RdHi == 15 or Rn == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && (dHi == n || dLo == n) then UNPREDICTABLE;
            if self.ArchVersion() < 6 and ((RdHi == Rn) or (RdLo == Rn)):
                raise UnpredictableInstructionException() 

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(RdLo), Register(RdHi), Register(Rn), Register(Rm)]
        ins = Instruction(ins_id, opcode, "SMULL", setflags, condition, operands, encoding)
        return ins
    
    def decode_smla(self, opcode, encoding):
        """
        A8.8.176
        SMLABB, SMLABT, SMLATB, SMLATT
        Signed Multiply Accumulate (halfwords) performs a signed multiply accumulate operation. The multiply acts on
        two signed 16-bit quantities, taken from either the bottom or the top half of their respective source registers. The
        other halves of these source registers are ignored. The 32-bit product is added to a 32-bit accumulate value and the
        result is written to the destination register.        
        
        Syntax:
        SMLA<x><y>{<c>}{<q>} <Rd>, <Rn>, <Rm>, <Ra>
        """
        props = {}        
        ins_id = ARMInstruction.smla
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Ra = get_bits(opcode, 15, 12)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            N = get_bit(opcode, 5)
            M = get_bit(opcode, 4)
            
            # if Ra == '1111' then SEE SMULBB, SMULBT, SMULTB, SMULTT;
            if Ra == 0b1111:
                return self.decode_smul(opcode, encoding)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} || a == 13 then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm) or Ra == 13:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 19, 16)
            Ra = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)

            N = get_bit(opcode, 5)
            M = get_bit(opcode, 6)            
            
            # if d == 15 || n == 15 || m == 15 || a == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15 or Ra == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        if N == 0 and M == 0:
            operands = [Register(Rd), Register(Rn), Register(Rm), Register(Ra)]
            ins = Instruction(ins_id, opcode, "SMLABB", False, condition, operands, encoding)

        elif N == 0 and M == 1:
            operands = [Register(Rd), Register(Rn), Register(Rm), Register(Ra)]
            ins = Instruction(ins_id, opcode, "SMLABT", False, condition, operands, encoding)
            
        elif N == 1 and M == 0:
            operands = [Register(Rd), Register(Rn), Register(Rm), Register(Ra)]
            ins = Instruction(ins_id, opcode, "SMLATB", False, condition, operands, encoding)
            
        elif N == 1 and M == 1:
            operands = [Register(Rd), Register(Rn), Register(Rm), Register(Ra)]
            ins = Instruction(ins_id, opcode, "SMLATT", False, condition, operands, encoding)
        
        return ins

    def decode_smlaw(self, opcode, encoding):
        """
        A8.8.181
        SMLAWB, SMLAWT
        Signed Multiply Accumulate (word by halfword) performs a signed multiply accumulate operation. The multiply
        acts on a signed 32-bit quantity and a signed 16-bit quantity. The signed 16-bit quantity is taken from either the
        bottom or the top half of its source register. The other half of the second source register is ignored. The top 32 bits
        of the 48-bit product are added to a 32-bit accumulate value and the result is written to the destination register. The
        bottom 16 bits of the 48-bit product are ignored.        
        
        Syntax:
        SMLAW<y>{<c>}{<q>} <Rd>, <Rn>, <Rm>, <Ra>
        """
        props = {}
        ins_id = ARMInstruction.smlaw
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Ra = get_bits(opcode, 15, 12)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            M = get_bit(opcode, 4)
            
            # if Ra == '1111' then SEE SMULWB, SMULWT;
            if Ra == 0b1111:
                return self.decode_smulw(opcode, encoding)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} || a == 13 then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm) or Ra == 13:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 19, 16)
            Ra = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)

            M = get_bit(opcode, 6)            
            
            # if d == 15 || n == 15 || m == 15 || a == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15 or Ra == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Register(Rm), Register(Ra)]
        
        if M:
            ins = Instruction(ins_id, opcode, "SMLAWT", False, condition, operands, encoding)
        else:
            ins = Instruction(ins_id, opcode, "SMLAWB", False, condition, operands, encoding)
        return ins

    def decode_smulw(self, opcode, encoding):
        """
        A8.8.190
        SMULWB, SMULWT
        Signed Multiply (word by halfword) multiplies a signed 32-bit quantity and a signed 16-bit quantity. The signed
        16-bit quantity is taken from either the bottom or the top half of its source register. The other half of the second
        source register is ignored. The top 32 bits of the 48-bit product are written to the destination register. The bottom
        16 bits of the 48-bit product are ignored. No overflow is possible during this instruction.        
        
        Syntax:
        SMULW<y>{<c>}{<q>} {<Rd>,} <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.smulw
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            # m_high = (M == '1');
            M = get_bit(opcode, 4)
            m_high = M == 1
                        
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)

            # m_high = (M == '1');
            M = get_bit(opcode, 6)            
            m_high = M == 1
            
            # if d == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        name = "SMULWT" if m_high else "SMULWB"
        operands = [Register(Rd), Register(Rn), Register(Rm)]
        ins = Instruction(ins_id, opcode, name, False, condition, operands, encoding)
        return ins

    def decode_smlalb(self, opcode, encoding):
        """
        A8.8.179
        SMLALBB, SMLALBT, SMLALTB, SMLALTT
        Signed Multiply Accumulate Long (halfwords) multiplies two signed 16-bit values to produce a 32-bit value, and
        accumulates this with a 64-bit value. The multiply acts on two signed 16-bit quantities, taken from either the bottom
        or the top half of their respective source registers. The other halves of these source registers are ignored. The 32-bit
        product is sign-extended and accumulated with a 64-bit accumulate value.        
        
        Syntax:
        SMLAL{S}{<c>}{<q>} <RdLo>, <RdHi>, <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.smlalb
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            RdHi = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            N = get_bit(opcode, 5)
            M = get_bit(opcode, 4)
                        
            # if dLo IN {13,15} || dHi IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(RdLo) or BadReg(RdHi) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            RdHi = get_bits(opcode, 19, 16)
            RdLo = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)

            N = get_bit(opcode, 5)
            M = get_bit(opcode, 6)
            
            # if dLo == 15 || dHi == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if RdLo == 15 or RdHi == 15 or Rn == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            # if dHi == dLo then UNPREDICTABLE;
            if RdHi == RdLo:
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && (dHi == n || dLo == n) then UNPREDICTABLE;
            if self.ArchVersion() < 6 and (RdHi == Rn or RdLo == Rn):
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(RdLo), Register(RdHi), Register(Rn), Register(Rm)]
        ins = Instruction(ins_id, opcode, "SMLAL", False, condition, operands, encoding)
        return ins

    def decode_smul(self, opcode, encoding):
        """
        A8.8.188
        SMULBB, SMULBT, SMULTB, SMULTT
        Signed Multiply (halfwords) multiplies two signed 16-bit quantities, taken from either the bottom or the top half of
        their respective source registers. The other halves of these source registers are ignored. The 32-bit product is written
        to the destination register. No overflow is possible during this instruction.   
        
        Syntax:
        SMUL<x><y>{<c>}{<q>} {<Rd>,} <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.smul
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            N = get_bit(opcode, 5)
            M = get_bit(opcode, 4)
                        
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 3, 0)

            N = get_bit(opcode, 5)
            M = get_bit(opcode, 6)
            
            # if d == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if N == 0 and M == 0:
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "SMULBB", False, condition, operands, encoding)

        elif N == 0 and M == 1:
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "SMULBT", False, condition, operands, encoding)
            
        elif N == 1 and M == 0:
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "SMULTB", False, condition, operands, encoding)
            
        elif N == 1 and M == 1:
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "SMULTT", False, condition, operands, encoding)
            
        return ins

    def decode_sat_add_and_sub(self, opcode, encoding):
        condition = self.decode_condition_field(opcode)
        raise InstructionNotImplementedException("decode_sat_add_and_sub")

    def decode_bx(self, opcode, encoding):
        """
        A8.8.27
        BX
        Branch and Exchange causes a branch to an address and instruction set specified by a register.
        
        Syntax:
        BX{<c>}{<q>} <Rm>
        """
        props = {}
        ins_id = ARMInstruction.bx
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 6, 3)
            
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
            
            operands = [Register(Rm)]
            ins = Instruction(ins_id, opcode, "BX", False, None, operands, encoding)
            
            condition = None
                        
        elif encoding == eEncodingA1:
            Rm = get_bits(opcode, 3, 0)

            operands = [Register(Rm)]
            ins = Instruction(ins_id, opcode, "BX", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_bxj(self, opcode, encoding):
        """
        A8.8.28
        BXJ
        Branch and Exchange Jazelle attempts to change to Jazelle state. If the attempt fails, it branches to an address and
        instruction set specified by a register as though it were a BX instruction.
        
        Syntax:
        BXJ{<c>}{<q>} <Rm>
        """
        props = {}
        ins_id = ARMInstruction.bxj
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 19, 16)
            
            # if m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rm):
                raise UnpredictableInstructionException()
            
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rm)]
            ins = Instruction(ins_id, opcode, "BXJ", False, None, operands, encoding)
                        
        elif encoding == eEncodingA1:
            Rm = get_bits(opcode, 3, 0)
            
            # if m == 15 then UNPREDICTABLE;
            if Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rm)]
            ins = Instruction(ins_id, opcode, "BXJ", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
    
        return ins
    
    def decode_cbz(self, opcode, encoding):
        """
        A8.8.29
        CBNZ, CBZ
        Compare and Branch on Nonzero and Compare and Branch on Zero compare the value in a register with zero, and
        conditionally branch forward a constant value. They do not affect the condition flags.
        
        Syntax:
        CB{N}Z{<q>} <Rn>, <label>
        """
        props = {}
        ins_id = ARMInstruction.cbz
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            op = get_bit(opcode, 11)
            i = get_bit(opcode, 9)
            imm5 = get_bits(opcode, 7, 3)
            Rn = get_bits(opcode, 2, 0)
            
            # imm32 = ZeroExtend(i:imm5:'0', 32);
            imm32 = ((i << 5) | imm5) << 1
            nonzero = op == 1
            
            # if InITBlock() then UNPREDICTABLE;
            if self.InITBlock():
                raise UnpredictableInstructionException()
            
            condition = None

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
    
        operands = [Register(Rn), Immediate(imm32)]
        if op == 1:
            ins = Instruction(ins_id, opcode, "CBNZ", False, condition, operands, encoding)
        else:
            ins = Instruction(ins_id, opcode, "CBZ", False, condition, operands, encoding)
            
        return ins
    
    def decode_clz(self, opcode, encoding):
        """
        A8.8.33
        CLZ
        Count Leading Zeros returns the number of binary zero bits before the first binary one bit in a value.
        
        Syntax:
        CLZ{<c>}{<q>} <Rd>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.clz
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 3, 0)
            Rd = get_bits(opcode, 11, 8)
            
            # TODO: No idea what Consistent stands for
            # if not Consistent(Rm):
            #     raise UnpredictableInstructionException()
            
            # if d IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rm) or BadReg(Rd):
                raise UnpredictableInstructionException()
            
            condition = None
                        
        elif encoding == eEncodingA1:
            Rm = get_bits(opcode, 3, 0)
            Rd = get_bits(opcode, 15, 12)

            # if d == 15 || m == 15 then UNPREDICTABLE;
            if Rm == 15 or Rd == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rm)]
        ins = Instruction(ins_id, opcode, "CLZ", False, condition, operands, encoding)
        return ins
        
    def decode_bkpt(self, opcode, encoding):
        """
        A8.8.24
        BKPT
        Breakpoint causes a software breakpoint to occur.
        Breakpoint is always unconditional, even when inside an IT block.
        
        Syntax:
        BKPT{<q>} {#}<imm>
        
        Unit-test: OK
        """
        props = {}        
        ins_id = ARMInstruction.bkpt
        if encoding == eEncodingT1:
            imm = get_bits(opcode, 7, 0)
            condition = None
            
        elif encoding == eEncodingA1:
            imm12 = get_bits(opcode, 19, 8)
            imm4 = get_bits(opcode, 3, 0)
            imm = (imm12 << 4) | imm4
            cond = get_bits(opcode, 31, 28)
            
            # if cond != '1110' then UNPREDICTABLE;
            if cond != 0b1110:
                raise UnpredictableInstructionException()
            
            condition = Condition(cond)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Immediate(imm)]
        ins = Instruction(ins_id, opcode, "BKPT", False, condition, operands, encoding)
        return ins
                    
    def decode_it(self, opcode, encoding):
        """
        A8.8.54
        IT
        If-Then makes up to four following instructions (the IT block) conditional. The conditions for the instructions in the
        IT block are the same as, or the inverse of, the condition the IT instruction specifies for the first instruction in the
        block.        
        
        Syntax:
        IT{<x>{<y>{<z>}}}{<q>} <firstcond>
        """
        props = {}
        ins_id = ARMInstruction.it
        if encoding == eEncodingT1:
            firstcond = get_bits(opcode, 7, 4)
            condition_mask = get_bits(opcode, 3, 0)
            
            # if condition_mask == '0000' then SEE "Related encodings";
            if condition_mask == 0b0000:
                opA = get_bits(opcode, 7, 4)
                opB = get_bits(opcode, 3, 0)
                
                if opA == 0b0000 and opB == 0b000:
                    return self.decode_nop(opcode, encoding)

                elif opA == 0b0001 and opB == 0b000:
                    return self.decode_yield(opcode, encoding)
                
                elif opA == 0b0010 and opB == 0b000:
                    return self.decode_wfe(opcode, encoding)
                
                elif opA == 0b0011 and opB == 0b000:
                    return self.decode_wfi(opcode, encoding)
                
                elif opA == 0b0100 and opB == 0b000:
                    return self.decode_sev(opcode, encoding)
                
                self.decode_yield(opcode, encoding)
            
            # if firstcond == '1111' || (firstcond == '1110' && BitCount(condition_mask) != 1) then UNPREDICTABLE;
            if firstcond == 0b1111 or (firstcond == 0b1110 and BitCount(condition_mask) != 1):
                raise UnpredictableInstructionException()
            
            if self.InITBlock():
                raise UnpredictableInstructionException()
            
            CondBit0 = firstcond & 1
            
            # (3 - the number of trailing zeros) is the number of then / else.
            trailing_zeros = CountTrailingZeros(condition_mask)
            
            conds = ""
            
            for position in xrange(trailing_zeros + 1, 3 + 1):
                T = ((condition_mask >> position) & 1) == CondBit0
              
                if (T):
                    conds = "T" + conds
                    
                else:
                    conds = "E" + conds

            condition = None
            operands = [Condition(firstcond)]                        
            ins = Instruction(ins_id, opcode, "IT" + conds, False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_blx_register(self, opcode, encoding):
        """
        A8.8.26
        BLX (register)
        Branch with Link and Exchange (register) calls a subroutine at an address and instruction set specified by a register.

        Syntax:
        BLX{<c>}{<q>} <Rm>

        Unit-test: OK
        """
        props = {}
        ins_id = ARMInstruction.blx_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 6, 3)
            
            # if m == 15 then UNPREDICTABLE;
            if Rm == 15:
                raise UnpredictableInstructionException()
            
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rm)]
            ins = Instruction(ins_id, opcode, "BLX", False, None, operands, encoding)
            
        elif encoding == eEncodingA1:
            Rm = get_bits(opcode, 3, 0)
            
            # if m == 15 then UNPREDICTABLE;
            if Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rm)]
            ins = Instruction(ins_id, opcode, "BLX", False, condition, operands, encoding)


        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_and_register(self, opcode, encoding):
        """
        A8.8.14   AND (register)
        This opcode performs a bitwise AND of a register value and an optionally-shifted register value, and writes the 
        result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        AND{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.and_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            # Encoding T1 ARMv4T | ARMv5TAll | ARMv6All | ARMv7
            # ANDS <Rdn>, <Rm> Outside IT block.
            # AND<c> <Rdn>, <Rm> Inside IT block
            Rd = get_bits(opcode, 2, 0)
            Rn = Rd
            Rm = get_bits(opcode, 5, 3)
            shift_t = SRType_LSL
            shift_n = 0
            setflags = not self.InITBlock()

            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "AND", setflags, condition, operands, encoding)                        

        elif encoding == eEncodingT2:
            # Encoding T2 ARMv6T2 | ARMv7
            # AND{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>}
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20) == 1
            shift_t, shift_n = DecodeImmShiftThumb(opcode)

            # if Rd == '1111' and S == '1' then SEE TST (register);
            if (Rd == 15 and setflags):
                return self.decode_tst_register(opcode, encoding)

            # if d == 13 || (d == 15 && S == '0') || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if (Rd == 13 or (Rd == 15 and not setflags) or BadReg(Rn) or BadReg(Rm)):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "AND", setflags, condition, operands, encoding, ".W")

        elif encoding == eEncodingA1:
            # Encoding A1 ARMv4All | ARMv5TAll | ARMv6All| ARMv7
            # AND{S}<c> <Rd>, <Rn>, <Rm>{, <shift>}
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)         
            setflags = get_bit(opcode, 20) == 1

            shift_t, shift_n = DecodeImmShiftARM(opcode)

            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)
            
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "AND", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_eor_register(self, opcode, encoding):
        """
        A8.8.47
        EOR (register)
        Bitwise Exclusive OR (register) performs a bitwise Exclusive OR of a register value and an optionally-shifted
        register value, and writes the result to the destination register. It can optionally update the condition flags based on
        the result.
        
        Syntax:
        EOR{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.eor_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            shift_t = SRType_LSL
            shift_n = 0

            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "EOR", setflags, condition, operands, encoding)

        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            
            # if Rd == '1111' and S == '1' then SEE TEQ (register);
            if (Rd == 15 and setflags):
                return self.decode_teq_register(opcode, encoding)
            
            # if d == 13 || (d == 15 && S == '0') || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if (Rd == 13 or (Rd == 15 and not setflags) or BadReg(Rn) or BadReg(Rm)):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "EOR", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            # if Rd == '1111' and S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "EOR", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins

    def decode_sub_sp_minus_immediate(self, opcode, encoding):
        """
        A8.8.225
        SUB (SP minus immediate)
        This instruction subtracts an immediate value from the SP value, and writes the result to the destination register.        
        """
        props = {}
        ins_id = ARMInstruction.sub_sp_minus_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            imm7 = get_bits(opcode, 6, 0) << 2
            setflags = False
            
            condition = None
            operands = [ARMRegister.SP, ARMRegister.SP, Immediate(imm7)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding)
        
        elif encoding == eEncodingT2:
            S = get_bit(opcode, 20)
            Rd = get_bits(opcode, 11, 8)
            imm32 = ThumbExpandImm(opcode)
            setflags = S == 1
            
            # if Rd == '1111' && S == '1' then SEE CMP (immediate);
            if Rd == 0b1111 and S == 1:
                return self.decode_cmp_immediate(opcode, encoding)
        
            # if d == 15 && S == '0' then UNPREDICTABLE;
            if Rd == 15 and S == 0:
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rd), ARMRegister.SP, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding, ".W")
        
        elif encoding == eEncodingT3:
            i = get_bit(opcode, 26)
            imm3 = get_bits(opcode, 14, 12)
            Rd = get_bits(opcode, 11, 8)
            imm8 = get_bits(opcode, 7, 0)
                        
            # imm32 = ZeroExtend(i:imm3:imm8, 32);
            imm32 = (i << (3 + 8)) | (imm3 << 8) | (imm8)
            print bin(i), bin(imm3), bin(imm8)
            print bin(imm32)
            
            #  if d == 15 then UNPREDICTABLE;
            if Rd == 15:
                raise UnpredictableInstructionException()
            
            setflags = False
            
            condition = None
            operands = [Register(Rd), ARMRegister.SP, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUBW", setflags, condition, operands, encoding)
        
        elif encoding == eEncodingA1:
            S = get_bit(opcode, 20)
            Rd = get_bits(opcode, 15, 12)
            imm32 = ARMExpandImm(opcode)
            setflags = S == 1
            
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 0b1111 and S == 1:
                return self.decode_subs_pc_lr_arm(opcode, encoding)
        
            operands = [Register(Rd), ARMRegister.SP, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_sub_sp_minus_register(self, opcode, encoding):
        """
        A8.8.226
        SUB (SP minus register)
        This instruction subtracts an optionally-shifted register value from the SP value, and writes the result to the
        destination register.        
        """
        props = {}
        ins_id = ARMInstruction.sub_sp_minus_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            S = get_bit(opcode, 20)
            imm3 = get_bits(opcode, 14, 12)
            Rd = get_bits(opcode, 11, 8)
            imm2 = get_bits(opcode, 7, 6)
            type_ = get_bits(opcode, 5, 4)
            Rm = get_bits(opcode, 3, 0)
            imm5 = (imm3 << 2) | imm2
            shift_t, shift_n = DecodeImmShift(type_, imm5)
            
            # if Rd == '1111' && S == '1' then SEE CMP (register);
            if Rd == 0b1111 and S == 1:
                return self.decode_cmp_register(opcode, encoding)
            
            setflags = S == 1
            
            # if d == 13 && (shift_t != SRType_LSL || shift_n > 3) then UNPREDICTABLE;
            if Rd == 13 and (shift_t != SRType_LSL or shift_n > 3):
                raise UnpredictableInstructionException()
        
            # if (d == 15 && S == '0') || m IN {13,15} then UNPREDICTABLE;
            if (Rd == 15 and S == 0) or (BadReg(Rm)):
                raise UnpredictableInstructionException()
            
            condition = None
                        
        elif encoding == eEncodingA1:
            S = get_bit(opcode, 20)
            Rd = get_bits(opcode, 15, 12)
            shift_t, shift_n = DecodeImmShiftARM(opcode)
            setflags = S == 1
            Rm = get_bits(opcode, 3, 0)
            
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 0b1111 and S == 1:
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), ARMRegister.SP, Register(Rm), RegisterShift(shift_t, shift_n)]
        ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding)
        
        return ins

    def decode_sub_register(self, opcode, encoding):
        """
        A8.8.223
        SUB (register)
        This instruction subtracts an optionally-shifted register value from a register value, and writes the result to the
        destination register. It can optionally update the condition flags based on the result.        
        
        Syntax:
        SUB{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.sub_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 2, 0)
            Rn = get_bits(opcode, 5, 3)
            Rm = get_bits(opcode, 8, 6)

            setflags = not self.InITBlock()
            shift_t = SRType_LSL
            shift_n = 0
            
            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding)

        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            
            # if Rd == '1111' && S == '1' then SEE CMP (register);
            if Rd == 0b1111 and setflags:
                return self.decode_cmp_register(opcode, encoding)
            
            # if Rn == '1101' then SEE SUB (SP minus register);
            if Rn == 0b1101:
                return self.decode_sub_sp_minus_register(opcode, eEncodingT1)
            
            # if d == 13 || (d == 15 && S == '0') || n == 15 || m IN {13,15} then UNPREDICTABLE;
            if (Rd == 13 or (Rd == 15 and not setflags) or Rn == 15 or BadReg(Rm)):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            # if Rd == '1111' and S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)
            
            # if Rn == '1101' then SEE SUB (SP minus register);
            if Rn == 0b1101:
                return self.decode_sub_sp_minus_register(opcode, encoding)

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins

    def decode_rsb_register(self, opcode, encoding):
        """
        A8.8.153
        RSB (register)
        Reverse Subtract (register) subtracts a register value from an optionally-shifted register value, and writes the result
        to the destination register. It can optionally update the condition flags based on the result.        
        
        Syntax:
        RSB{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.rsb_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)

            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)

            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if (BadReg(Rd) or BadReg(Rn) or BadReg(Rm)):
                raise UnpredictableInstructionException()
            
            condition = None

        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            # if Rd == '1111' and S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
        ins = Instruction(ins_id, opcode, "RSB", setflags, condition, operands, encoding)
        return ins

    def decode_add_register_arm(self, opcode, encoding):
        """
        A8.8.7
        ADD (register, ARM)
        This instruction adds a register value and an optionally-shifted register value, and writes the result to the destination
        register. It can optionally update the condition flags based on the result.        
        
        Syntax:
        ADD{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.add_register
        condition = self.decode_condition_field(opcode)
        
        S = get_bit(opcode, 20)
        Rn = get_bits(opcode, 19, 16)
        Rd = get_bits(opcode, 15, 12)
        Rm = get_bits(opcode, 3, 0)
        setflags = S == 1
        shift_t, shift_n = DecodeImmShiftARM(opcode)

        # if Rd == '1111' and S == '1' then SEE SUBS PC, LR and related instructions;
        if Rd == 15 and setflags:
            # NOTE: In the spec there is no information about what encoding
            # should be used here.
            encoding = eEncodingA2
            return self.decode_subs_pc_lr_arm(opcode, encoding)

        # if Rn == '1101' then SEE ADD (SP plus register);
        if Rn == 13:
            return self.decode_add_sp_plus_register_arm(opcode, encoding)

        operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
        ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)
        return ins
                
    def decode_add_register_thumb(self, opcode, encoding):
        """
        A8.8.6
        ADD (register, Thumb)
        This instruction adds a register value and an optionally-shifted register value, and writes the result to the destination
        register. It can optionally update the condition flags based on the result.
        
        Syntax:
        ADD{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.add_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            # ADD (register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
            Rm = get_bits(opcode, 8, 6)
            Rn = get_bits(opcode, 5, 3)
            Rd = get_bits(opcode, 2, 0)

            setflags = not self.InITBlock()
            shift_t = SRType_LSL
            shift_n = 0
            
            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            # ADD (register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
            Rd = Rn = get_bit(opcode, 7) << 3 | get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 6, 3)
            
            setflags = 0
            shift_t = SRType_LSL
            shift_n = 0
            
            # if (DN:Rdn) == '1101' or Rm == '1101' then SEE ADD (SP plus register);
            if Rd == 13 or Rm == 13:
                return self.decode_add_sp_plus_register_thumb(opcode, encoding)
            
            # if n == 15 && m == 15 then UNPREDICTABLE;
            if (Rn == 15 and Rm == 15):
                raise UnpredictableInstructionException()
            
            # if d == 15 && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if (Rd == 15 and self.InITBlock() and not self.LastInITBlock()):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)
        
        elif encoding == eEncodingT3:
            S = get_bit(opcode, 20)
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            # if Rd == '1111' && S == '1' then SEE CMN (register);
            if Rd == 0b1111 and S == 1:
                # NOTE: CMN does not support T3 encoding
                return self.decode_cmn_register(opcode, encoding)
            
            # if Rn == '1101' then SEE ADD (SP plus register);
            if Rn == 0b1101:
                return self.decode_add_sp_plus_register_thumb(opcode, encoding)
            
            setflags = S == 1
            
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            
            # if d == 13 || (d == 15 && S == '0') || n == 15 || m IN {13,15} then UNPREDICTABLE;
            if Rd == 13 or (Rd == 15 and S == 0) or Rn == 15 or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_adc_register(self, opcode, encoding):
        """
        A8.8.2
        ADC (register)
        Add with Carry (register) adds a register value, the Carry flag value, and an optionally-shifted register value, and
        writes the result to the destination register. It can optionally update the condition flags based on the result.

        Syntax:
        ADC{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.adc_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            setflags = not self.InITBlock()
            shift_t = SRType_LSL
            shift_n = 0
            
            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ADC", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
                        
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "ADC", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 0b1111 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "ADC", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_sbc_register(self, opcode, encoding):
        """
        A8.8.162
        SBC (register)
        Subtract with Carry (register) subtracts an optionally-shifted register value and the value of NOT (Carry flag) from
        a register value, and writes the result to the destination register. It can optionally update the condition flags based
        on the result.
        
        Syntax:
        SBC{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.sbc_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            setflags = not self.InITBlock()
            shift_t = SRType_LSL
            shift_n = 0
            
            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "SBC", setflags, condition, operands, encoding)

        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
                        
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "SBC", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "SBC", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_rsc_register(self, opcode, encoding):
        """
        A8.8.156
        RSC (register)
        Reverse Subtract with Carry (register) subtracts a register value and the value of NOT (Carry flag) from an
        optionally-shifted register value, and writes the result to the destination register. It can optionally update the
        condition flags based on the result.
        
        Syntax:
        RSC{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.rsc_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            # if Rd == '1111' and S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
        ins = Instruction(ins_id, opcode, "RSC", setflags, condition, operands, encoding)
        return ins

    def decode_tst_register(self, opcode, encoding):
        """
        A8.8.241
        TST (register)
        Test (register) performs a bitwise AND operation on a register value and an optionally-shifted register value. It
        updates the condition flags based on the result, and discards the result.
        
        Syntax:
        TST{<c>}{<q>} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.tst_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            shift_t = SRType_LSL
            shift_n = 0

            condition = None
            operands = [Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "TST", False, condition, operands, encoding)

        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            
            # if n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "TST", False, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "TST", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_teq_register(self, opcode, encoding):
        """
        A8.8.238
        TEQ (register)
        Test Equivalence (register) performs a bitwise exclusive OR operation on a register value and an optionally-shifted
        register value. It updates the condition flags based on the result, and discards the result.
        
        Syntax:
        TEQ{<c>}{<q>} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.teq_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)

            shift_t, shift_n = DecodeImmShiftThumb(opcode)

            # if n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rn) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
        ins = Instruction(ins_id, opcode, "TEQ", False, condition, operands, encoding)
        return ins

    def decode_cmp_register(self, opcode, encoding):
        """
        A8.8.38
        CMP (register)
        Compare (register) subtracts an optionally-shifted register value from a register value. It updates the condition flags
        based on the result, and discards the result.
        
        Syntax:
        CMP{<c>}{<q>} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.cmp_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            shift_t = SRType_LSL
            shift_n = 0
            
            condition = None
            operands = [Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "CMP", False, condition, operands, encoding)

        elif encoding == eEncodingT2:
            Rn = get_bit(opcode, 7) << 3 | get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 6, 3)
            shift_t = SRType_LSL
            shift_n = 0
            
            # if n < 8 && m < 8 then UNPREDICTABLE;
            if (Rn < 8 and Rm < 8):
                raise UnpredictableInstructionException()
            
            # if n == 15 || m == 15 then UNPREDICTABLE;
            if (Rn == 15 or Rm == 15):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "CMP", False, condition, operands, encoding)
            
        elif encoding == eEncodingT3:
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            
            # if n == 15 || m IN {13,15} then UNPREDICTABLE;
            if Rn == 15 or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "CMP", False, condition, operands, encoding, ".W")
        
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "CMP", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_cmn_register(self, opcode, encoding):
        """
        A8.8.35
        CMN (register)
        Compare Negative (register) adds a register value and an optionally-shifted register value. It updates the condition
        flags based on the result, and discards the result.

        Syntax:
        CMN{<c>}{<q>} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.cmn_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            shift_t = SRType_LSL
            shift_n = 0
            
            condition = None
            operands = [Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "CMN", False, condition, operands, encoding)

        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
                        
            # if n == 15 || m IN {13,15} then UNPREDICTABLE;
            if Rn == 15 or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "CMN", False, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "CMN", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_orr_register(self, opcode, encoding):
        """
        8.8.123
        ORR (register)
        Bitwise OR (register) performs a bitwise (inclusive) OR of a register value and an optionally-shifted register value,
        and writes the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        ORR{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.orr_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            setflags = not self.InITBlock()
            shift_t = SRType_LSL
            shift_n = 0

            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ORR", setflags, condition, operands, encoding)

        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            
            # if Rn == '1111' then SEE "Related encodings";
            if Rn == 15:
                imm3 = get_bits(opcode, 14, 12)
                imm2 = get_bits(opcode, 7, 6)
                type_ = get_bits(opcode, 5, 4)
                
                tmp = (imm3 << 2) | imm2
                
                if type_ == 0b00:
                    if tmp == 0b00000:
                        return self.decode_mov_register_thumb(opcode, encoding)
                    
                    else:
                        return self.decode_lsl_immediate(opcode, encoding)

                elif type_ == 0b01:
                    return self.decode_lsr_immediate(opcode, encoding)

                elif type_ == 0b10:
                    return self.decode_asr_immediate(opcode, encoding)

                elif type_ == 0b11:
                    if tmp == 0b00000:
                        return self.decode_rrx(opcode, encoding)
                    
                    else:
                        return self.decode_ror_immediate(opcode, encoding)
                                    
            # if d IN {13,15} || n == 13 || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or Rn == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "ORR", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)

            # if Rd == '1111' and S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "ORR", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_mov_register_thumb(self, opcode, encoding):
        """
        A8.8.103
        MOV (register, Thumb)
        
        Move (register) copies a value from a register to the destination register. It can optionally update the condition flags
        based on the value.
        
        Syntax:
        MOV{S}{<c>}{<q>} <Rd>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.mov_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            D = get_bit(opcode, 7)
            Rm = get_bits(opcode, 6, 3)
            Rd = (D << 3) | get_bits(opcode, 2, 0)
            
            if Rd == 15 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
            
            setflags = False
            
            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "MOV", setflags, condition, operands, encoding)                
        
        elif encoding == eEncodingT2:
            Rm = get_bits(opcode, 5, 3)
            Rd = get_bits(opcode, 2, 0)
            
            if self.InITBlock():
                raise UnpredictableInstructionException()
            
            setflags = True
            
            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "MOV", setflags, condition, operands, encoding)                
        
        elif encoding == eEncodingT3:
            S = get_bit(opcode, 20)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            setflags = S == 1
            
            if setflags and (BadReg(Rd) or BadReg(Rm)):
                raise UnpredictableInstructionException()
            
            if not setflags and (Rd == 15 or Rm == 15 or (Rd == 13 and Rm == 13)):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "MOV", setflags, condition, operands, encoding)                

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_mov_register_arm(self, opcode, encoding):
        """
        A8.8.104
        MOV (register, ARM)
        Move (register) copies a value from a register to the destination register. It can 
        optionally update the condition flags based on the value.

        Syntax:
        MOV{S}{<c>}{<q>} <Rd>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.mov_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            s = get_bit(opcode, 20)
            
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 0b1111 and s == 0b1:                
                return self.decode_subs_pc_lr_arm(opcode, encoding)
            
            setflags = s == 1

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rm)]
        ins = Instruction(ins_id, opcode, "MOV", setflags, condition, operands, encoding)
        return ins

    def decode_lsl_register(self, opcode, encoding):
        """
        A8.8.95
        LSL (register)
        Logical Shift Left (register) shifts a register value left by a variable number of bits, shifting in zeros, and writes the
        result to the destination register. The variable number of bits is read from the bottom byte of a register. It can
        optionally update the condition flags based on the result.
        
        Syntax:
        LSL{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.lsl_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            
            condition = None
            operands = [Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "LSL", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm) or BadReg(Rn):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "LSL", setflags, condition, operands, encoding, ".W")
                        
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 3, 0)
            Rm = get_bits(opcode, 11, 8)
            setflags = get_bit(opcode, 20)

            # if d == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if (Rd == 15 or Rn == 15 or Rm == 15):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "LSL", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins

    def decode_lsr_register(self, opcode, encoding):
        """
        A8.8.97
        LSR (register)
        Logical Shift Right (register) shifts a register value right by a variable number of bits, shifting in zeros, and writes
        the result to the destination register. The variable number of bits is read from the bottom byte of a register. It can
        optionally update the condition flags based on the result.
        
        Syntax:
        LSR{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.lsr_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            
            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "LSR", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm) or BadReg(Rn):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "LSR", setflags, condition, operands, encoding, ".W")
                        
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 3, 0)
            Rm = get_bits(opcode, 11, 8)
            setflags = get_bit(opcode, 20)

            # if d == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if (Rd == 15 or Rn == 15 or Rm == 15):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "LSR", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_asr_register(self, opcode, encoding):
        """
        A8.8.17
        ASR (register)
        Arithmetic Shift Right (register) shifts a register value right by a variable number of bits, shifting in copies of its
        sign bit, and writes the result to the destination register. The variable number of bits is read from the bottom byte of
        a register. It can optionally update the condition flags based on the result.

        Syntax:
        ASR{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>
        """
        props = {}
        ins_id = ARMInstruction.asr_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()

            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ASR", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm) or BadReg(Rn):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ASR", setflags, condition, operands, encoding)
                        
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 3, 0)
            Rm = get_bits(opcode, 11, 8)
            setflags = get_bit(opcode, 20)

            # if d == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if (Rd == 15 or Rn == 15 or Rm == 15):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ASR", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_rrx(self, opcode, encoding):
        """
        A8.8.151
        RRX
        Rotate Right with Extend provides the value of the contents of a register shifted right by one place, with the Carry
        flag shifted into bit[31].
        
        Syntax:
        RRX{S}{<c>}{<q>} {<Rd>,} <Rm>
        """
        props = {}
        ins_id = ARMInstruction.rrx
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)

            # if d IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)

            # if Rd == '1111' and S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        operands = [Register(Rd), Register(Rm)]
        ins = Instruction(ins_id, opcode, "RRX", setflags, condition, operands, encoding)
        return ins

    def decode_ror_register(self, opcode, encoding):
        """
        A8.8.150
        ROR (register)
        Rotate Right (register) provides the value of the contents of a register rotated by a variable number of bits. The bits
        that are rotated off the right end are inserted into the vacated bit positions on the left. The variable number of bits is
        read from the bottom byte of a register. It can optionally update the condition flags based on the result.
        
        Syntax:
        ROR{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>
        """
        props = {}        
        ins_id = ARMInstruction.ror_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            
            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ROR", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm) or BadReg(Rn):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ROR", setflags, condition, operands, encoding, ".W")
                        
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 3, 0)
            Rm = get_bits(opcode, 11, 8)
            setflags = get_bit(opcode, 20)

            # if d == 15 || n == 15 || m == 15 then UNPREDICTABLE;
            if (Rd == 15 or Rn == 15 or Rm == 15):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "ROR", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_bic_register(self, opcode, encoding):
        """
        A8.8.22
        BIC (register)
        Bitwise Bit Clear (register) performs a bitwise AND of a register value and the complement of an optionally-shifted
        register value, and writes the result to the destination register. It can optionally update the condition flags based on
        the result.
        
        Syntax:
        BIC{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.bic_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            # BIC (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
            Rd = Rn = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            
            shift_t = SRType_LSL
            shift_n = 0

            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "BIC", setflags, condition, operands, encoding)

        elif encoding == eEncodingT2:
            # BIC (register) ARMv6T2 | ARMv7
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            
            # if d IN {13,15} || n IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm) or BadReg(Rn):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "BIC", setflags, condition, operands, encoding, ".W")
                                    
        elif encoding == eEncodingA1:
            # BIC (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7 
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)
            
            # if Rd == '1111' and S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "BIC", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_mvn_register(self, opcode, encoding):
        """
        A8.8.116
        MVN (register)
        Bitwise NOT (register) writes the bitwise inverse of a register value to the destination register. It can optionally
        update the condition flags based on the result.
        
        Syntax:
        MVN{S}{<c>}{<q>} <Rd>, <Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.mvn_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            
            shift_t = SRType_LSL
            shift_n = 0

            condition = None
            operands = [Register(Rd), Register(Rm)]
            ins = Instruction(ins_id, opcode, "MVN", setflags, condition, operands, encoding)

        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            
            # if d IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "MVN", setflags, condition, operands, encoding, ".W")
                        
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftARM(opcode)
            
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: In the spec there is no information about what encoding
                # should be used here.
                encoding = eEncodingA2                
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            operands = [Register(Rd), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "MVN", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins

    def decode_data_processing_xxx_reg_shift_reg(self, ins_id, opcode, encoding, opstr):
        """
        """
        props = {}
        condition = self.decode_condition_field(opcode)
        
        # Generic routine to parse reg shift reg instructions
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 15, 12)
            Rs = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t = get_bits(opcode, 6, 5)
            
            # if d == 15 || n == 15 || m == 15 || s == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15 or Rs == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
        ins = Instruction(ins_id, opcode, opstr, setflags, condition, operands, encoding)
        return ins

    def decode_data_processing_xxx_reg_shift_reg_test(self, ins_id, opcode, encoding, opstr):
        """
        """
        props = {}
        condition = self.decode_condition_field(opcode)
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rs = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            shift_t = get_bits(opcode, 6, 5)
            
            if Rn == 15 or Rm == 15 or Rs == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
        ins = Instruction(ins_id, opcode, opstr, False, condition, operands, encoding)
        return ins        
    
    def decode_and_rsr(self, opcode, encoding):
        """
        A8.8.15
        AND (register-shifted register)
        This instruction performs a bitwise AND of a register value and a register-shifted register value. It writes the result
        to the destination register, and can optionally update the condition flags based on the result.        
        
        Syntax:
        AND{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.and_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "AND")
    
    def decode_eor_rsr(self, opcode, encoding):
        """
        A8.8.48
        EOR (register-shifted register)
        Bitwise Exclusive OR (register-shifted register) performs a bitwise Exclusive OR of a register value and a
        register-shifted register value. It writes the result to the destination register, and can optionally update the condition
        flags based on the result.
        
        Syntax:
        OR{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.eor_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "EOR")
            
    def decode_sub_rsr(self, opcode, encoding):
        """
        A8.8.224
        SUB (register-shifted register)
        This instruction subtracts a register-shifted register value from a register value, and writes the result to the
        destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        SUB{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.sub_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "SUB")
    
    def decode_rsb_rsr(self, opcode, encoding):
        """
        A8.8.154
        RSB (register-shifted register)
        Reverse Subtract (register-shifted register) subtracts a register value from a register-shifted register value, and
        writes the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        RSB{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}        
        ins_id = ARMInstruction.rsb_rsr
        condition = self.decode_condition_field(opcode)

        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 15, 12)
            Rs = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t = get_bits(opcode, 6, 5)
            
            # if d == 15 || n == 15 || m == 15 || s == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15 or Rs == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
        ins = Instruction(ins_id, opcode, "RSB", setflags, condition, operands, encoding)
        return ins
    
    def decode_subs_pc_lr_arm(self, opcode, encoding):
        """
        B9.3.20
        SUBS PC, LR and related instructions, ARM
        The SUBS PC, LR, #<const> instruction provides an exception return without the use of the stack. It subtracts the
        immediate constant from LR, branches to the resulting address, and also copies the SPSR to the CPSR. The ARM
        instruction set contains similar instructions based on other data-processing operations, or with a wider range of
        operands, or both. ARM deprecates using these other instructions, except for MOVS PC, LR.
                
        Syntax:
        """
        props = {}
        ins_id = ARMInstruction.subs_pc_lr
        condition = self.decode_condition_field(opcode)
        
        register_form = encoding == eEncodingA2
        
        opc1 = False
        opc2 = False
        opc3 = False
        
        op = get_bits(opcode, 24, 21)
        if op == 0b0000:
            name = "AND"
            opc1 = True
        elif op == 0b0001:
            name = "EOR"
            opc1 = True
        elif op == 0b0010:
            name = "SUB"
            opc1 = True
        elif op == 0b0011:
            name = "RSB"
            opc1 = True
        elif op == 0b0100:
            name = "ADD"
            opc1 = True
        elif op == 0b0101:
            name = "ADC"
            opc1 = True
        elif op == 0b0110:
            name = "SBC"
            opc1 = True
        elif op == 0b0111:
            name = "RSC"
            opc1 = True
        elif op == 0b1100:
            name = "ORR"
            opc1 = True
        elif op == 0b1101:
            if not register_form:
                name = "MOV"
                opc2 = True
            else:
                name = "MOV"
                opc3 = True
                
        elif op == 0b1110:
            name = "BIC"
            opc1 = True
        elif op == 0b1111:
            name = "MVN"
            opc2 = True
        else:
            name = "CUNT"
        
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            imm32 = ARMExpandImm(opcode)
            register_form = False
         
            operands = [ARMRegister.PC, Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, name, True, condition, operands, encoding)
         
        elif encoding == eEncodingA2:
            Rn = get_bits(opcode, 19, 16)
            shift_t, shift_n = DecodeImmShiftARM(opcode)
            Rm = get_bits(opcode, 3, 0)
            register_form = True

            operands = [ARMRegister.PC, Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, name, True, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins
    
    def decode_subs_pc_lr_thumb(self, opcode, encoding):
        """
        B9.3.19
        SUBS PC, LR, Thumb
        The SUBS PC, LR, #<const> instruction provides an exception return without the use of the stack. It subtracts the
        immediate constant from LR, branches to the resulting address, and also copies the SPSR to the CPSR.
        
        Syntax:
        SUBS{<c>}{<q>} PC, LR, #<const>
        """
        props = {}
        ins_id = ARMInstruction.subs_pc_lr
        imm8 = get_bits(opcode, 7, 0)
        
        # if IsZero(imm8) then SEE ERET;
        if imm8 == 0:
            return self.decode_eret(opcode, encoding)
        
        # TODO:
        # if CurrentInstrSet() == InstrSet_ThumbEE then UNPREDICTABLE;
        # if CurrentModeIsHyp() then UNDEFINED;
               
        # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
        if self.InITBlock() and not self.LastInITBlock():
            raise UnpredictableInstructionException()
        
        operands = [ARMRegister.PC, ARMRegister.LR, Immediate(imm8)]
        ins = Instruction(ins_id, opcode, "SUBS", False, None, operands, encoding)
        return ins
    
    def decode_add_sp_plus_immediate(self, opcode, encoding):
        """
        A8.8.9
        ADD (SP plus immediate)
        This instruction adds an immediate value to the SP value, and writes the result to the destination register.
        
        Syntax:
        ADD{S}{<c>}{<q>} {<Rd>,} SP, #<const> All encodings permitted
        ADDW{<c>}{<q>} {<Rd>,} SP, #<const>   Only encoding T4 is permitted
        """
        props = {}
        ins_id = ARMInstruction.add_sp_plus_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 10, 8)
            imm8 = get_bits(opcode, 7, 0)
            setflags = False
            imm32 = imm8 << 2

            condition = None
            operands = [Register(Rd), ARMRegister.SP, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)            
        
        elif encoding == eEncodingT2:
            imm7 = get_bits(opcode, 6, 0)
            imm32 = imm7 << 2
            Rd = 13
            setflags = False

            condition = None
            operands = [ARMRegister.SP, ARMRegister.SP, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)            
        
        elif encoding == eEncodingT3:
            S = get_bit(opcode, 20)
            Rd = get_bits(opcode, 11, 8)
            imm32 = ThumbExpandImm(opcode)
            setflags = S == 1

            # if Rd == '1111' && S == '1' then SEE CMN (immediate);
            if Rd == 0b1111 and S == 1:
                # NOTE: CMN does not support T3 encoding
                return self.decode_cmn_immediate(opcode, encoding)

            # if d == 15 && S == '0' then UNPREDICTABLE;
            if Rd == 15 and S == 0:
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), ARMRegister.SP, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding, ".W")            
        
        elif encoding == eEncodingT4:
            i = get_bit(opcode, 26)
            S = get_bit(opcode, 20)
            imm3 = get_bits(opcode, 14, 12)
            Rd = get_bits(opcode, 11, 8)
            imm8 = get_bits(opcode, 7, 0)
            imm32 = (i << 11) | (imm3 << 8) | imm8
        
            # if d == 15 then UNPREDICTABLE;    
            if Rd == 15:
                raise UnpredictableInstructionException()
            
            setflags = S == 1

            condition = None
            operands = [Register(Rd), ARMRegister.SP, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADDW", setflags, condition, operands, encoding)            
        
        elif encoding == eEncodingA1:
            S = get_bit(opcode, 20)
            Rd = get_bits(opcode, 15, 12)
            
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 0b1111 and S == 1:
                return self.decode_subs_pc_lr_arm(opcode, encoding)
            
            setflags = S == 1
            imm32 = ARMExpandImm(opcode)

            operands = [Register(Rd), ARMRegister.SP, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)            

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
    
    def decode_add_sp_plus_register_thumb(self, opcode, encoding):
        """
        A8.8.10
        ADD (SP plus register, Thumb)
        This instruction adds an optionally-shifted register value to the SP value, and writes the result to the destination
        register.
        
        Syntax:
        ADD{S}{<c>}{<q>} {<Rd>,} SP, <Rm>{, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.add_sp_plus_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            DM = get_bit(opcode, 7)
            Rdm = get_bits(opcode, 2, 0)
            
            # Rm = Rd = DM:Rdm
            Rm = Rd = (DM << 3) | Rdm
            setflags = False
            
            # if d == 15 && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if Rd == 15 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
            
            shift_t = SRType_LSL
            shift_n = 0

            condition = None
            operands = [Register(Rd), ARMRegister.SP, Register(Rm)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)            
            
        elif encoding == eEncodingT2:
            Rm = get_bits(opcode, 6, 3)
            
            # if Rm == '1101' then SEE encoding T1;
            if Rm == 0b1101:
                DM = get_bit(opcode, 7)
                Rdm = get_bits(opcode, 2, 0)
                
                # Rm = Rd = DM:Rdm
                Rm = Rd = (DM << 3) | Rdm
                setflags = False
                
                # if d == 15 && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
                if Rd == 15 and self.InITBlock() and not self.LastInITBlock():
                    raise UnpredictableInstructionException()
                
                shift_t = SRType_LSL
                shift_n = 0

                condition = None
                operands = [Register(Rd), ARMRegister.SP, Register(Rm)]
                ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)                  

            else:
                Rd = 13
                setflags = False
                shift_t = SRType_LSL
                shift_n = 0

                condition = None
                operands = [Register(Rd), Register(Rm)]
                ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)                  
                        
        elif encoding == eEncodingT3:
            S = get_bit(opcode, 20)
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            
            # if Rd == '1111' && S == '1' then SEE CMN (register);
            if Rd == 0b1111 and S == 1:
                return self.decode_cmn_register(opcode, encoding)
            
            setflags = S == 1
            
            # if d == 13 && (shift_t != SRType_LSL || shift_n > 3) then UNPREDICTABLE;
            if Rd == 13 and (shift_t != SRType_LSL or shift_n > 3):
                raise UnpredictableInstructionException()
            
            # if (d == 15 && S == '0') || m IN {13,15} then UNPREDICTABLE;
            if (Rd == 15 and S == 0) or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), ARMRegister.SP, Register(Rm), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding, ".W")                  

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
    
    def decode_add_sp_plus_register_arm(self, opcode, encoding):
        """
        A8.8.11
        ADD (SP plus register, ARM)
        This instruction adds an optionally-shifted register value to the SP value, and writes the result to the destination
        register.
        
        Syntax:
        ADD{S}{<c>}{<q>} {<Rd>,} SP, <Rm>{, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.add_sp_plus_register
        condition = self.decode_condition_field(opcode)
        
        S = get_bit(opcode, 20)
        Rd = get_bits(opcode, 15, 12)
        Rm = get_bits(opcode, 3, 0)
        shift_t, shift_n = DecodeImmShiftARM(opcode)

        # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
        if Rd == 0b1111 and S == 1:
            # NOTE: In the spec there is no information about what encoding
            # should be used here.
            encoding = eEncodingA2            
            return self.decode_subs_pc_lr_arm(opcode, encoding)
        
        setflags = S == 1

        operands = [Register(Rd), ARMRegister.SP, Register(Rm), RegisterShift(shift_t, shift_n)]
        ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)            

        return ins
        
    def decode_add_rsr(self, opcode, encoding):
        """
        A8.8.8
        ADD (register-shifted register)
        Add (register-shifted register) adds a register value and a register-shifted register value. It writes the result to the
        destination register, and can optionally update the condition flags based on the result.

        Syntax: 
        ADD{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.add_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "ADD")
    
    def decode_adc_rsr(self, opcode, encoding):
        """
        A8.8.2
        ADC (register)
        Add with Carry (register) adds a register value, the Carry flag value, and an optionally-shifted register value, and
        writes the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        ADC{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.adc_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "ADC")
    
    def decode_sbc_rsr(self, opcode, encoding):
        """
        A8.8.163
        SBC (register-shifted register)
        Subtract with Carry (register-shifted register) subtracts a register-shifted register value and the value of NOT (Carry
        flag) from a register value, and writes the result to the destination register. It can optionally update the condition
        flags based on the result.
        
        Syntax:
        SBC{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.sbc_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "SBC")
        
    def decode_rsc_rsr(self, opcode, encoding):
        """
        A8.8.157
        RSC (register-shifted register)
        Reverse Subtract (register-shifted register) subtracts a register value and the value of NOT (Carry flag) from a
        register-shifted register value, and writes the result to the destination register. It can optionally update the condition
        flags based on the result.
        
        Syntax:
        RSC{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.rsc_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "RSC")
    
    def decode_tb(self, opcode, encoding):
        """
        A8.8.236 
        TBB, TBH

        Table Branch Byte causes a PC-relative forward branch using a table of single byte offsets. A base register provides
        a pointer to the table, and a second register supplies an index into the table. The branch length is twice the value of
        the byte returned from the table.
        Table Branch Halfword causes a PC-relative forward branch using a table of single halfword offsets. A base register
        provides a pointer to the table, and a second register supplies an index into the table. The branch length is twice the
        value of the halfword returned from the table.
        
        TBB{<c>}{<q>} [<Rn>, <Rm>]
        TBH{<c>}{<q>} [<Rn>, <Rm>, LSL #1]        
        """
        props = {}
        ins_id = ARMInstruction.tb
        Rn = get_bits(opcode, 19, 16)
        H = get_bit(opcode, 4)
        Rm = get_bits(opcode, 3, 0)
        
        # is_tbh = (H == '1');
        is_tbh = H == 1
        
        # if n == 13 || m IN {13,15} then UNPREDICTABLE;
        if Rn == 13 or BadReg(Rm):
            raise UnpredictableInstructionException()
    
        # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
        if self.InITBlock() and not self.LastInITBlock():
            raise UnpredictableInstructionException()

        if is_tbh:
            operands = [Register(Rn), Register(Rm), RegisterShift(SRType_LSL, 1)]
            ins = Instruction(ins_id, opcode, "TBH", False, None, operands, encoding)
        
        else:
            operands = [Register(Rn), Register(Rm)]
            ins = Instruction(ins_id, opcode, "TBB", False, None, operands, encoding)
        
        return ins        
            
    
    def decode_tst_rsr(self, opcode, encoding):
        """
        A8.8.242
        TST (register-shifted register)
        Test (register-shifted register) performs a bitwise AND operation on a register value and a register-shifted register
        value. It updates the condition flags based on the result, and discards the result.
        
        Syntax:
        ST{<c>}{<q>} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.tst_rsr
        return self.decode_data_processing_xxx_reg_shift_reg_test(ins_id, opcode, encoding, "TST")
    
    def decode_teq_rsr(self, opcode, encoding):
        """
        A8.8.239
        TEQ (register-shifted register)
        Test Equivalence (register-shifted register) performs a bitwise exclusive OR operation on a register value and a
        register-shifted register value. It updates the condition flags based on the result, and discards the result.
        
        Syntax:
        TEQ{<c>}{<q>} <Rn>, <Rm>, <type> <Rs>   
        """
        props = {}
        ins_id = ARMInstruction.teq_rsr
        return self.decode_data_processing_xxx_reg_shift_reg_test(ins_id, opcode, encoding, "TEQ")
    
    def decode_cmp_rsr(self, opcode, encoding):
        """
        A8.8.39
        CMP (register-shifted register)
        Compare (register-shifted register) subtracts a register-shifted register value from a register value. It updates the
        condition flags based on the result, and discards the result.
        
        Syntax:
        CMP{<c>}{<q>} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.cmp_rsr
        return self.decode_data_processing_xxx_reg_shift_reg_test(ins_id, opcode, encoding, "CMP")
    
    def decode_cmn_rsr(self, opcode, encoding):
        """
        A8.8.36
        CMN (register-shifted register)
        Compare Negative (register-shifted register) adds a register value and a register-shifted register value. It updates the
        condition flags based on the result, and discards the result.
        
        Syntax:
        CMN{<c>}{<q>} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.cmn_rsr

        return self.decode_data_processing_xxx_reg_shift_reg_test(ins_id, opcode, encoding, "CMN")
    
    def decode_orr_rsr(self, opcode, encoding):
        """
        A8.8.124
        ORR (register-shifted register)
        Bitwise OR (register-shifted register) performs a bitwise (inclusive) OR of a register value and a register-shifted
        register value, and writes the result to the destination register. It can optionally update the condition flags based on
        the result.
        
        Syntax:
        ORR{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.orr_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "ORR")

    def decode_mov_rsr(self, opcode, encoding):
        ins_id = ARMInstruction.mov_rsr
        raise InstructionNotImplementedException("decode_mov_rsr")
                
    def decode_bic_rsr(self, opcode, encoding):
        """
        A8.8.23
        BIC (register-shifted register)
        Bitwise Bit Clear (register-shifted register) performs a bitwise AND of a register value and the complement of a
        register-shifted register value. It writes the result to the destination register, and can optionally update the condition
        flags based on the result.
        
        Syntax:
        BIC{S}{<c>}{<q>} {<Rd>,} <Rn>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.bic_rsr
        return self.decode_data_processing_xxx_reg_shift_reg(ins_id, opcode, encoding, "BIC")

    def decode_mvn_rsr(self, opcode, encoding):
        """
        A8.8.117
        MVN (register-shifted register)
        Bitwise NOT (register-shifted register) writes the bitwise inverse of a register-shifted register value to the
        destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        MVN{S}{<c>}{<q>} <Rd>, <Rm>, <type> <Rs>
        """
        props = {}
        ins_id = ARMInstruction.mvn_rsr
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 15, 12)
            Rs = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            shift_t = get_bits(opcode, 6, 5)
            
            # if d == 15 || m == 15 || s == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15 or Rm == 15 or Rs == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rm), RegisterShift(shift_t, Register(Rs))]
        ins = Instruction(ins_id, opcode, "MVN", setflags, condition, operands, encoding)
        return ins

    def decode_and_immediate(self, opcode, encoding):
        """
        A8.8.13
        AND (immediate)
        This instruction performs a bitwise AND of a register value and an immediate value, and writes the result to the
        destination register.
        
        Syntax:
        AND{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.and_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            S = get_bit(opcode, 20)
            setflags = S == 1
            
            # if Rd == '1111' && S == '1' then SEE TST (immediate);
            if Rd == 0b1111 and S == 1:
                return self.decode_tst_immediate(opcode, encoding)
            
            # (imm32, carry) = ThumbExpandImm(i:imm3:imm8, APSR.C)
            imm32, _ = ThumbExpandImm_C(opcode, 0) 
            
            # if d == 13 || (d == 15 && S == '0') || n IN {13,15} then UNPREDICTABLE;
            if (Rd == 13 or (Rd == 15 and not setflags) or BadReg(Rn)):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            
            # (imm32, carry) = ARMExpandImm(imm12, APSR.C)
            imm32, _ = ARMExpandImm_C(opcode, 0) 
 
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "AND", setflags, condition, operands, encoding)                        
        return ins
        
    def decode_eor_immediate(self, opcode, encoding):
        """
        A8.8.46
        EOR (immediate)
        Bitwise Exclusive OR (immediate) performs a bitwise Exclusive OR of a register value and an immediate value,
        and writes the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        EOR{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.eor_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            S = get_bit(opcode, 20)
            setflags = S == 1
            
            # if Rd == '1111' && S == '1' then SEE TEQ (immediate);
            if Rd == 0b1111 and S == 1:
                return self.decode_teq_immediate(opcode, encoding)
            
            # (imm32, carry) = ThumbExpandImm(i:imm3:imm8, APSR.C)
            imm32, _ = ThumbExpandImm_C(opcode, 0) 
            
            # if d == 13 || (d == 15 && S == '0') || n IN {13,15} then UNPREDICTABLE;
            if (Rd == 13 or (Rd == 15 and not setflags) or BadReg(Rn)):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            
            # (imm32, carry) = ARMExpandImm(imm12, APSR.C)
            imm32, _ = ARMExpandImm_C(opcode, 0) 
 
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "EOR", setflags, condition, operands, encoding)
        return ins
                
    def decode_adr(self, opcode, encoding):
        """
        A8.8.12
        ADR
        This instruction adds an immediate value to the PC value to form a PC-relative address, and writes the result to the
        destination register.
        
        Syntax:        
        ADR{<c>}{<q>} <Rd>, <label>        Normal syntax
        ADD{<c>}{<q>} <Rd>, PC, #<const>   Alternative for encodings T1, T3, A1
        SUB{<c>}{<q>} <Rd>, PC, #<const>   Alternative for encoding T2, A2
        """
        props = {}
        ins_id = ARMInstruction.adr
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 10, 8)
            imm32 = get_bits(opcode, 7, 0) << 2
            
            condition = None
            operands = [Register(Rd), ARMRegister.PC, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", False, condition, operands, encoding)                        
             
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            
            imm3 = get_bits(opcode, 14, 12)
            imm8 = get_bits(opcode, 7, 0)
            i = get_bit(opcode, 26)
            
            # imm32 = ZeroExtend(i:imm3:imm8, 32)
            imm32 = (i << (3 + 8)) + (imm3 << 8) + imm8
            
            # if d IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), ARMRegister.PC, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUB", False, condition, operands, encoding)                        
            
        elif encoding == eEncodingT3:
            Rd = get_bits(opcode, 11, 8)
            
            imm3 = get_bits(opcode, 14, 12)
            imm8 = get_bits(opcode, 7, 0)
            i = get_bit(opcode, 26)
            
            # imm32 = ZeroExtend(i:imm3:imm8, 32)
            imm32 = (i << (3 + 8)) + (imm3 << 8) + imm8
            
            # if d IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), ARMRegister.PC, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", False, condition, operands, encoding)                        
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            imm32 = ARMExpandImm(opcode)
            
            operands = [Register(Rd), ARMRegister.PC, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", False, condition, operands, encoding)                        
    
        elif encoding == eEncodingA2:
            Rd = get_bits(opcode, 15, 12)
            imm32 = ARMExpandImm(opcode)

            operands = [Register(Rd), ARMRegister.PC, Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUB", False, condition, operands, encoding)                        

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins
    
    def decode_sub_immediate_arm(self, opcode, encoding):
        """
        A8.8.222
        SUB (immediate, ARM)
        This instruction subtracts an immediate value from a register value, and writes the result to the destination register.
        It can optionally update the condition flags based on the result.
    
        Syntax:
        SUB{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.sub_immediate
        condition = self.decode_condition_field(opcode)
        
        S = get_bit(opcode, 20)
        Rn = get_bits(opcode, 19, 16)
        Rd = get_bits(opcode, 15, 12)
        imm32 = ARMExpandImm(opcode)
        
        # if Rn == '1111' && S == '0' then SEE ADR;
        if Rn == 0b1111 and S == 1:
            # NOTE: Encoding changed to A2 since we are in sub.
            encoding = eEncodingA2
            return self.decode_adr(opcode, encoding)

        # if Rn == '1101' then SEE SUB (SP minus immediate);
        if Rn == 0b1101:
            return self.decode_sub_sp_minus_immediate(opcode, encoding)
        
        # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
        if Rd == 0b1111 and S == 1:
            return self.decode_subs_pc_lr_arm(opcode, encoding)
        
        setflags = S == 1
        
        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding)
        return ins
    
    def decode_sub_immediate_thumb(self, opcode, encoding):
        """
        A8.8.221
        SUB (immediate, Thumb)
        This instruction subtracts an immediate value from a register value, and writes the result to the destination register.
        It can optionally update the condition flags based on the result.

        Syntax:
        SUB{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>    All encodings permitted
        SUBW{<c>}{<q>} {<Rd>,} <Rn>, #<const>      Only encoding T4 permitted
        """
        props = {}
        ins_id = ARMInstruction.sub_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 2, 0)
            Rn = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            imm32 = get_bits(opcode, 8, 6);
            
            condition = None
            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = Rn = get_bits(opcode, 10, 8)
            setflags = not self.InITBlock()
            imm32 = get_bits(opcode, 7, 0)

            condition = None
            operands = [Register(Rd), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT3:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32 = ThumbExpandImm(opcode)
    
            # if Rd == '1111' and S == '1' then SEE CMP (immediate)
            if (Rd == 15 and setflags):
                return self.decode_cmp_immediate(opcode, encoding)                
    
            # if Rn == '1101' then SEE SUB (SP minus immediate);
            if (Rn == 13):
                return self.decode_sub_sp_minus_immediate(opcode, eEncodingT2)
    
            # if d == 13 or (d == 15 and S == '0') or n == 15 then UNPREDICTABLE;
            if (Rd == 13 or (Rd == 15 and not setflags) or Rn == 15):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingT4:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32 = ThumbImm12(opcode)
    
            # if Rn == '1111' then SEE ADR;
            if (Rn == 15):
                return self.decode_adr(opcode, encoding)
    
            # if Rn == '1101' then SEE SUB (SP minus immediate);
            if (Rn == 13):
                return self.decode_sub_sp_minus_immediate(opcode, encoding)
    
            # if d IN {13,15} then UNPREDICTABLE;
            if (BadReg(Rd)):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "SUB", setflags, condition, operands, encoding, ".W")

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins                
        
    def decode_rsb_immediate(self, opcode, encoding):
        """
        A8.8.152
        RSB (immediate)
        Reverse Subtract (immediate) subtracts a register value from an immediate value, and writes the result to the
        destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        RSB{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.rsb_immediate
        condition = self.decode_condition_field(opcode)
                
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 2, 0)
            Rn = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            imm32 = 0
            
            condition = None
            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "RSB", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            
            # imm32 = ThumbExpandImm(i:imm3:imm8)
            imm32 = ThumbExpandImm(opcode) 
            
            # if d IN {13,15} || n IN {13,15} then UNPREDICTABLE;
            if (BadReg(Rd) or BadReg(Rn)):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "RSB", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            
            # imm32 = ARMExpandImm(imm12)
            imm32 = ARMExpandImm(opcode)
    
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "RSB", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                
        return ins

    def decode_add_immediate_thumb(self, opcode, encoding):
        """
        A8.8.4
        ADD (immediate, Thumb)
        This instruction adds an immediate value to a register value, and writes the result to the destination register. It can
        optionally update the condition flags based on the result.
        
        Syntax:
        ADD{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>    All encodings permitted
        ADDW{<c>}{<q>} {<Rd>,} <Rn>, #<const>      Only encoding T4 permitted
        """
        props = {}
        ins_id = ARMInstruction.add_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 2, 0)
            Rn = get_bits(opcode, 5, 3)
            setflags = not self.InITBlock()
            
            # imm32 = ZeroExtend(imm3, 32)
            imm32 = get_bits(opcode, 8, 6);

            condition = None
            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)
             
        elif encoding == eEncodingT2:
            Rd = Rn = get_bits(opcode, 10, 8)
            setflags = not self.InITBlock()
            
            # imm32 = ZeroExtend(imm8, 32)
            imm32 = get_bits(opcode, 7, 0)

            condition = None
            operands = [Register(Rd), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT3:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            
            # imm32 = ThumbExpandImm(i:imm3:imm8)
            imm32 = ThumbExpandImm(opcode)
    
            # if Rd == '1111' && S == '1' then SEE CMN (immediate);
            if (Rd == 15 and setflags):
                # NOTE: CMN does not support T3 encoding
                return self.decode_cmn_immediate(opcode, encoding)                
    
            # if Rn == '1101' then SEE ADD (SP plus immediate);
            if (Rn == 13):
                return self.decode_add_sp_plus_immediate(opcode, encoding)
    
            # if d == 13 or (d == 15 and S == '0') or n == 15 then UNPREDICTABLE;
            if (Rd == 13 or (Rd == 15 and not setflags) or Rn == 15):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingT4:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = 0
            
            # imm32 = ZeroExtend(i:imm3:imm8, 32)
            imm32 = ThumbImm12(opcode)
    
            # if Rn == '1111' then SEE ADR;
            if (Rn == 15):
                # NOTE: ADR does not support T4 encoding
                return self.decode_adr(opcode, encoding)
    
            # if Rn == '1101' then SEE ADD (SP plus immediate);
            if (Rn == 13):
                return self.decode_add_sp_plus_immediate(opcode, encoding)
    
            # if d IN {13,15} then UNPREDICTABLE;
            if (BadReg(Rd)):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "ADDW", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
    
    def decode_add_immediate_arm(self, opcode, encoding):
        """
        A8.8.5
        ADD (immediate, ARM)
        This instruction adds an immediate value to a register value, and writes the result to the destination register. It can
        optionally update the condition flags based on the result.
        
        Syntax:
        ADD{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.add_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32 = ARMExpandImm(opcode) 
    
            # if Rn == '1111' && S == '0' then SEE ADR;
            if (Rn == 15 and not setflags):
                return self.decode_adr(opcode, encoding)
    
            # if Rn == '1101' then SEE ADD (SP plus immediate);
            if (Rn == 13):
                return self.decode_add_sp_plus_immediate(opcode, encoding)
    
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: The specs are not clear here. I've chosen the ARM decode
                # since we are already decoding ARM but the spec does not specify
                # either one.
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "ADD", setflags, condition, operands, encoding)
        return ins
    
    def decode_adc_immediate(self, opcode, encoding):
        """
        A8.8.1
        ADC (immediate)
        Add with Carry (immediate) adds an immediate value and the Carry flag value to a register value, and writes the
        result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        ADC{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.adc_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32 = ThumbExpandImm(opcode) 
            
            # if d IN {13,15} || n IN {13,15} then UNPREDICTABLE;
            if (BadReg(Rd) or BadReg(Rn)):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32 = ARMExpandImm(opcode) 
 
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                # NOTE: it is not clear on the specs whether to call ARM version or THUMB.
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "ADC", setflags, condition, operands, encoding)
        return ins
        
    def decode_sbc_immediate(self, opcode, encoding):
        """
        A8.8.161
        SBC (immediate)
        Subtract with Carry (immediate) subtracts an immediate value and the value of NOT (Carry flag) from a register
        value, and writes the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        SBC{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.sbc_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32 = ThumbExpandImm(opcode) 
            
            # if d IN {13,15} || n IN {13,15} then UNPREDICTABLE;
            if (BadReg(Rd) or BadReg(Rn)):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32 = ARMExpandImm(opcode) 
 
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "SBC", setflags, condition, operands, encoding)
        return ins
        
    def decode_rsc_immediate(self, opcode, encoding):
        """
        A8.8.155
        RSC (immediate)
        Reverse Subtract with Carry (immediate) subtracts a register value and the value of NOT (Carry flag) from an
        immediate value, and writes the result to the destination register. It can optionally update the condition flags based
        on the result.
        
        Syntax:
        RSC{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.rsc_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32 = ARMExpandImm(opcode) 
 
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if (Rd == 15 and setflags):
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                    
        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "RSC", setflags, condition, operands, encoding)
        return ins
        
    def decode_tst_immediate(self, opcode, encoding):
        """
        A8.8.240
        TST (immediate)
        Test (immediate) performs a bitwise AND operation on a register value and an immediate value. It updates the
        condition flags based on the result, and discards the result.
        
        Syntax:
        TST{<c>}{<q>} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.tst_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            setflags = False
            imm32, _ = ThumbExpandImm_C(opcode, 0) 
            
            # if n IN {13,15} then UNPREDICTABLE;
            if BadReg(Rn):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            setflags = False
            imm32, _ = ARMExpandImm_C(opcode, 0) 

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "TST", setflags, condition, operands, encoding)
        return ins
        
    def decode_teq_immediate(self, opcode, encoding):
        """
        A8.8.237
        TEQ (immediate)
        Test Equivalence (immediate) performs a bitwise exclusive OR operation on a register value and an immediate
        value. It updates the condition flags based on the result, and discards the result.
        
        Syntax:
        TEQ{<c>}{<q>} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.teq_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            setflags = False
            imm32, _ = ThumbExpandImm_C(opcode, 0) 
            
            # if n IN {13,15} then UNPREDICTABLE;
            if BadReg(Rn):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            setflags = False
            imm32, _ = ARMExpandImm_C(opcode, 0) 

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "TEQ", setflags, condition, operands, encoding)
        return ins
        
    def decode_cmp_immediate(self, opcode, encoding):
        """
        A8.8.37
        CMP (immediate)
        Compare (immediate) subtracts an immediate value from a register value. It updates the condition flags based on
        the result, and discards the result.
        
        Syntax:
        CMP{<c>}{<q>} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.cmp_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 10, 8)
            imm32 = get_bits(opcode, 7, 0)
            
            condition = None
            operands = [Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "CMP", False, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            imm32 = ThumbExpandImm(opcode)
            
            # if n == 15 then UNPREDICTABLE;
            if BadReg(Rn):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "CMP", False, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            imm32 = ARMExpandImm(opcode)    

            operands = [Register(Rn), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "CMP", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
        
    def decode_cmn_immediate(self, opcode, encoding):
        """
        A8.8.34
        CMN (immediate)
        Compare Negative (immediate) adds a register value and an immediate value. It updates the condition flags based
        on the result, and discards the result.
        
        Syntax:
        CMN{<c>}{<q>} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.cmn_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            imm32 = ThumbExpandImm(opcode)
            
            # if n == 15 then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            imm32 = ARMExpandImm(opcode)
        
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "CMN", False, condition, operands, encoding)
        return ins
        
    def decode_orr_immediate(self, opcode, encoding):
        """
        A8.8.122
        ORR (immediate)
        Bitwise OR (immediate) performs a bitwise (inclusive) OR of a register value and an immediate value, and writes
        the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        ORR{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.orr_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32, _ = ThumbExpandImm_C(opcode, 0)
            
            # if Rn == '1111' then SEE MOV (immediate);
            if Rn == 0b1111:
                return self.decode_mov_immediate(opcode, encoding)
            
            # if d IN {13,15} || n == 13 then UNPREDICTABLE;            
            if BadReg(Rd) or Rn == 13:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
            imm32, _ = ARMExpandImm_C(opcode, 0) 
            
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 15 and setflags:
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "ORR", setflags, condition, operands, encoding)
        return ins
        
    def decode_nop(self, opcode, encoding):
        """
        A8.8.119
        NOP
        No Operation does nothing. This instruction can be used for instruction alignment purposes
        
        Syntax:
        NOP{<c>}{<q>}   
        """
        props = {}
        ins_id = ARMInstruction.nop
        condition = self.decode_condition_field(opcode)
        operands = []
        
        if encoding == eEncodingT1:
            condition = None
            ins = Instruction(ins_id, opcode, "NOP", False, None, operands, encoding)
            
        elif encoding == eEncodingT2:
            condition = None
            ins = Instruction(ins_id, opcode, "NOP", False, None, operands, encoding, ".W")
        
        elif encoding == eEncodingA1:
            ins = Instruction(ins_id, opcode, "NOP", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins
    
    def decode_yield(self, opcode, encoding):
        """
        A8.8.426
        YIELD
        YIELD is a hint instruction. Software with a multithreading capability can use a YIELD instruction to indicate to the
        hardware that it is performing a task, for example a spin-lock, that could be swapped out to improve overall system
        performance. Hardware can use this hint to suspend and resume multiple software threads if it supports the
        capability.
        
        Syntax:       
        YIELD{<c>}{<q>} 
        """
        props = {}
        ins_id = ARMInstruction.yield_
        condition = self.decode_condition_field(opcode)
        
        operands = []
        if encoding == eEncodingT1:
            condition = None
            ins = Instruction(ins_id, opcode, "YIELD", False, condition, operands, encoding)
        
        elif encoding == eEncodingT2:
            condition = None
            ins = Instruction(ins_id, opcode, "YIELD", False, condition, operands, encoding, ".W")
        
        elif encoding == eEncodingA1:
            ins = Instruction(ins_id, opcode, "YIELD", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
        
    def decode_wfe(self, opcode, encoding):
        """
        A8.8.424
        WFE
        Wait For Event is a hint instruction that permits the processor to enter a low-power state until one of a number of
        events occurs, including events signaled by executing the SEV instruction on any processor in the multiprocessor
        system.
        
        Syntax:
        WFE{<c>}{<q>}
        """
        props = {}
        ins_id = ARMInstruction.wfe
        condition = self.decode_condition_field(opcode)
        
        operands = []
        if encoding == eEncodingT1:
            condition = None
            ins = Instruction(ins_id, opcode, "WFE", False, condition, operands, encoding)
        
        elif encoding == eEncodingT2:
            condition = None
            ins = Instruction(ins_id, opcode, "WFE", False, condition, operands, encoding, ".W")
        
        elif encoding == eEncodingA1:
            ins = Instruction(ins_id, opcode, "WFE", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_wfi(self, opcode, encoding):
        """
        A8.8.425
        WFI
        Wait For Interrupt is a hint instruction that permits the processor to enter a low-power state until one of a number
        of asynchronous events occurs.
        
        Syntax: 
        WFI{<c>}{<q>}
        """
        props = {}
        ins_id = ARMInstruction.wfi
        condition = self.decode_condition_field(opcode)
        
        operands = []
        if encoding == eEncodingT1:
            condition = None
            ins = Instruction(ins_id, opcode, "WFI", False, condition, operands, encoding)
        
        elif encoding == eEncodingT2:
            condition = None
            ins = Instruction(ins_id, opcode, "WFI", False, condition, operands, encoding, ".W")
        
        elif encoding == eEncodingA1:
            ins = Instruction(ins_id, opcode, "WFI", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_vldr(self, opcode, encoding):
        """
        A8.8.333
        VLDR
        This instruction loads a single extension register from memory, using an address
        from an ARM core register, with an optional offset.
        Depending on settings in the CPACR, NSACR, HCPTR, and FPEXC registers, and the 
        security state and mode in which the instruction is executed, an attempt to execute 
        the instruction might be UNDEFINED, or trapped to Hyp mode. Summary of general controls 
        of CP10 and CP11 functionality on page B1-1226 and Summary of access controls for Advanced 
        SIMD functionality on page B1-1228 summarize these controls.        
        """
        props = {}        
        name = "VLDR"
        ins_id = ARMInstruction.vldr
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I8, 1, 1, I2, 4, 4, I4, 8]
            U, D, Rn, Vd, imm8 = decode_opcode(opcode, decode_mask)

            # single_reg = FALSE; add = (U == '1'); imm32 = ZeroExtend(imm8:'00', 32);
            single_reg = False
            add = U == 1
            imm32 = imm8 << 2

            # d = UInt(D:Vd); n = UInt(Rn);
            Dd = (D << 4) | Vd

            if not add:
                imm32 *= -1

            operands = [DRegister(Dd), Memory(Register(Rn), Immediate(imm32))]
        
        elif encoding == eEncodingT2:
            decode_mask = [I8, 1, 1, I2, 4, 4, I4, 8]
            U, D, Rn, Vd, imm8 = decode_opcode(opcode, decode_mask)

            # single_reg = FALSE; add = (U == '1'); imm32 = ZeroExtend(imm8:'00', 32);
            single_reg = False
            add = U == 1
            imm32 = imm8 << 2

            # d = UInt(Vd:D); n = UInt(Rn);
            Dd = (Vd << 1) | D

            if not add:
                imm32 *= -1

            operands = [DRegister(Dd), Memory(Register(Rn), Immediate(imm32))]

        elif encoding == eEncodingA1:
            decode_mask = [4, I4, 1, 1, I2, 4, 4, I4, 8]
            cond, U, D, Rn, Vd, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            # single_reg = FALSE; add = (U == '1'); imm32 = ZeroExtend(imm8:'00', 32);
            single_reg = False
            add = U == 1
            imm32 = imm8 << 2

            # d = UInt(D:Vd); n = UInt(Rn);
            Dd = (D << 4) | Vd

            if not add:
                imm32 *= -1

            operands = [DRegister(Dd), Memory(Register(Rn), Immediate(imm32))]

        elif encoding == eEncodingA2:
            decode_mask = [4, I4, 1, 1, I2, 4, 4, I4, 8]
            cond, U, D, Rn, Vd, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            # single_reg = FALSE; add = (U == '1'); imm32 = ZeroExtend(imm8:'00', 32);
            single_reg = False
            add = U == 1
            imm32 = imm8 << 2

            # d = UInt(Vd:D); n = UInt(Rn);
            Dd = (Vd << 1) | D

            if not add:
                imm32 *= -1

            operands = [SRegister(Dd), Memory(Register(Rn), Immediate(imm32))]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_unknown(self, opcode, encoding):
        """
        Default value for instructions we do not know how to decode.
        """
        props = {}
        ins_id = ARMInstruction.unknown
        ins = Instruction(ins_id, opcode, "UNK", False, None, [], encoding)
        return ins
    
    def decode_uxtb(self, opcode, encoding):
        """
        A8.8.274
        UXTB
        Unsigned Extend Byte extracts an 8-bit value from a register, zero-extends it to 32 bits, and writes the result to the
        destination register. The instruction can specify a rotation by 0, 8, 16, or 24 bits before extracting the 8-bit value.        
        """
        props = {}
        condition = None
        ins_id = ARMInstruction.uxtb
        qualifiers = ""
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 5, 3)
            Rd = get_bits(opcode, 2, 0)
            rotation = 0
            operands = [Register(Rd), Register(Rm)]
        
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            rotation = get_bits(opcode, 5, 4) << 3
            Rm = get_bits(opcode, 3, 0)
            
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            qualifiers = ".W"
            operands = [Register(Rd), Register(Rm), RegisterShift(SRType_ROR, rotation)]
        
        elif encoding == eEncodingA1:
            condition = self.decode_condition_field(opcode)
            
            Rd = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            rotation = get_bits(opcode, 11, 10) << 3
            
            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            
            Rm = get_bits(opcode, 3, 0)
            operands = [Register(Rd), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        ins = Instruction(ins_id, opcode, "UXTB", False, condition, operands, encoding, qualifiers)
        return ins
            
    def decode_ubfx(self, opcode, encoding):
        """
        A8.8.246
        UBFX
        Unsigned Bit Field Extract extracts any number of adjacent bits at any position from a register, zero-extends them
        to 32 bits, and writes the result to the destination register.        
        """
        props = {}
        ins_id = ARMInstruction.ubfx
        
        if encoding == eEncodingT1:
            condition = None
            # UBFX<c> <Rd>, <Rn>, #<lsb>, #<width>
            Rn = get_bits(opcode, 19, 16)
            imm3 = get_bits(opcode, 14, 12)
            Rd = get_bits(opcode, 11, 8)
            imm2 = get_bits(opcode, 7, 6)
            widthm1 = get_bits(opcode, 4, 0)
            
            # lsbit = UInt(imm3:imm2); widthminus1 = UInt(widthm1);
            lsbit = imm3 << 2 | imm2
            widthminus1 = widthm1 + 1
            
            # if d IN {13,15} || n IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn):
                raise UnpredictableInstructionException()
        
        elif encoding == eEncodingA1:
            # UBFX<c> <Rd>, <Rn>, #<lsb>, #<width>
            condition = self.decode_condition_field(opcode)
            
            # lsbit = UInt(lsb); widthminus1 = UInt(widthm1);
            widthminus1 = get_bits(opcode, 20, 16) + 1
            Rd = get_bits(opcode, 15, 12)
            lsbit = get_bits(opcode, 11, 7)
            Rn = get_bits(opcode, 3, 0)

            # if d == 15 || n == 15 then UNPREDICTABLE;
            if Rd == 15 or Rn == 15:
                raise UnpredictableInstructionException()

        operands = [Register(Rd), Register(Rn), Immediate(lsbit), Immediate(widthminus1)]
        ins = Instruction(ins_id, opcode, "UBFX", False, condition, operands, encoding)
        return ins

    def decode_sev(self, opcode, encoding):
        """
        A8.8.168
        SEV
        Send Event is a hint instruction. It causes an event to be signaled to all processors in the multiprocessor system.
        
        Syntax: 
        SEV{<c>}{<q>}
        """
        props = {}
        ins_id = ARMInstruction.sev
        condition = self.decode_condition_field(opcode)
               
        if encoding == eEncodingT1:
            condition = None
            ins = Instruction(ins_id, opcode, "SEV", False, condition, [], encoding)
        
        elif encoding == eEncodingT2:
            condition = None
            ins = Instruction(ins_id, opcode, "SEV", False, condition, [], encoding, ".W")
        
        elif encoding == eEncodingA1:
            ins = Instruction(ins_id, opcode, "SEV", False, condition, [], encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins

    def decode_dbg(self, opcode, encoding):
        """
        A8.8.42
        DBG
        Debug Hint provides a hint to debug and related systems.
        
        Syntax:
        DBG{<c>}{<q>} #<option>
        """
        props = {}
        ins_id = ARMInstruction.dbg
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            option = get_bits(opcode, 3, 0)
            
        elif encoding == eEncodingA1:
            option = get_bits(opcode, 3, 0)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Immediate(option)]
        ins = Instruction(ins_id, opcode, "DBG", False, condition, operands, encoding)
        return ins
        
    def decode_movt(self, opcode, encoding):
        """
        A8.8.106
        MOVT
        Move Top writes an immediate value to the top halfword of the destination register. It does not affect the contents
        of the bottom halfword.        
        
        Syntax:
        MOVT{<c>}{<q>} <Rd>, #<imm16>
        """
        props = {}
        ins_id = ARMInstruction.movt
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            i = get_bit(opcode, 26)
            imm4 = get_bits(opcode, 19, 16)
            imm3 = get_bits(opcode, 14, 12)
            Rd = get_bits(opcode, 11, 8)
            imm8 = get_bits(opcode, 7, 0)
            
            # imm16 = imm4:i:imm3:imm8;
            imm16 = (imm4 << (1 + 3 + 8)) + (i << (3 + 8)) + (imm3 << (8)) + imm8
            
            # if d IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            imm4 = get_bits(opcode, 19, 16)
            Rd = get_bits(opcode, 15, 12)
            imm12 = get_bits(opcode, 11, 0)
            
            # imm16 = imm4:imm12;
            imm16 = (imm4 << 12) + imm12
            
            # if d == 15 then UNPREDICTABLE;
            if Rd == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Immediate(imm16)]
        ins = Instruction(ins_id, opcode, "MOVT", False, condition, operands, encoding)
        return ins
        
    def decode_mov_immediate(self, opcode, encoding):
        """
        A8.8.102
        MOV (immediate)
        Move (immediate) writes an immediate value to the destination register. It can optionally update the condition flags
        based on the value.
        
        Syntax:
        MOV{S}{<c>}{<q>} <Rd>, #<const>  All encodings permitted
        MOVW{<c>}{<q>} <Rd>, #<const>    Only encoding T3 or A2 permitted
        """
        props = {}
        ins_id = ARMInstruction.mov_immediate
        condition = self.decode_condition_field(opcode)
                
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 10, 8)
            setflags = not self.InITBlock()
            imm32 = get_bits(opcode, 7, 0)
            
            condition = None
            operands = [Register(Rd), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "MOV", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            setflags = get_bit(opcode, 20)
            imm32, _ = ThumbExpandImm_C(opcode, 0)
            
            # if d IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "MOV", setflags, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingT3:
            Rd = get_bits(opcode, 11, 8)
            setflags = 0

            imm4 = get_bits(opcode, 19, 16)
            imm3 = get_bits(opcode, 14, 12)
            i = get_bit(opcode, 26)
            imm8 = get_bits(opcode, 7, 0)
            
            imm32 = (imm4 << 12) | (i << 11) | (imm3 << 8) | imm8
              
            # if d IN {13,15} then UNPREDICTABLE;
            if BadReg (Rd):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rd), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "MOVW", setflags, condition, operands, encoding)

        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            setflags = get_bit(opcode, 20)
            imm32, _ = ARMExpandImm_C(opcode, 0)
            
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 0b1111 and setflags:
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            operands = [Register(Rd), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "MOV", setflags, condition, operands, encoding)

        elif encoding == eEncodingA2:
            Rd = get_bits(opcode, 15, 12)
            setflags = 0
            
            imm4 = get_bits(opcode, 19, 16)
            imm12 = get_bits(opcode, 11, 0)
            imm32 = (imm4 << 12) | imm12
              
            # if d == 15 then UNPREDICTABLE;
            if Rd == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "MOVW", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins
        
    def decode_lsl_immediate(self, opcode, encoding):
        """
        A8.8.94
        LSL (immediate)
        Logical Shift Left (immediate) shifts a register value left by an immediate number of bits, shifting in zeros, and
        writes the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        LSL{S}{<c>}{<q>} {<Rd>,} <Rm>, #<imm5>
        """
        props = {}
        ins_id = ARMInstruction.lsl_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            setflags = not self.InITBlock()
            imm5 = get_bits(opcode, 10, 6)
            
            # if imm5 == '00000' then SEE MOV (register);
            if imm5 == 0:
                return self.decode_mov_register_thumb(opcode, encoding)
            
            condition = None
            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "LSL", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            imm5 = get_bits(opcode, 14, 12) << 2 | get_bits(opcode, 7, 6)

            # if (imm3:imm2) == '00000' then SEE MOV (register);
            if imm5 == 0:
                return self.decode_mov_register_thumb(opcode, encoding)
            
            # if d IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "LSL", setflags, condition, operands, encoding, ".W")

        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            
            imm5 = get_bits(opcode, 11, 7)
            # t, imm5 = DecodeImmShift(0b00, imm5)

            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 15 and setflags:
                return self.decode_subs_pc_lr_arm(opcode, encoding)
            
            # if imm5 == '00000' then SEE MOV (register);
            if imm5 == 0:
                return self.decode_mov_register_arm(opcode, encoding)

            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "LSL", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
        
    def decode_lsr_immediate(self, opcode, encoding):
        """
        A8.8.96
        LSR (immediate)
        Logical Shift Right (immediate) shifts a register value right by an immediate number of bits, shifting in zeros, and
        writes the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        LSR{S}{<c>}{<q>} {<Rd>,} <Rm>, #<imm>
        """
        props = {}
        ins_id = ARMInstruction.lsr_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            setflags = not self.InITBlock()
            imm5 = get_bits(opcode, 10, 6)
            
            condition = None
            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "LSR", setflags, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            imm5 = get_bits(opcode, 14, 12) << 2 | get_bits(opcode, 7, 6)

            # if d IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "LSR", setflags, condition, operands, encoding, ".W")

        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            _, imm5 = DecodeImmShiftARM(opcode)
                    
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 15 and setflags:
                return self.decode_subs_pc_lr_arm(opcode, encoding)        

            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "LSR", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
        
    def decode_asr_immediate(self, opcode, encoding):
        """
        A8.8.16
        ASR (immediate)
        Arithmetic Shift Right (immediate) shifts a register value right by an immediate number of bits, shifting in copies
        of its sign bit, and writes the result to the destination register. It can optionally update the condition flags based on
        the result.
        
        Syntax:
        ASR{S}{<c>}{<q>} {<Rd>,} <Rm>, #<imm>
        """
        props = {}
        ins_id = ARMInstruction.asr_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 2, 0)
            Rm = get_bits(opcode, 5, 3)

            setflags = not self.InITBlock()
            imm5 = get_bits(opcode, 10, 6)
            _, imm5 = DecodeImmShift(0b10, imm5)

            condition = None
            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "ASR", setflags, condition, operands, encoding)            
            
        elif encoding == eEncodingT2:
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            imm5 = get_bits(opcode, 14, 12) << 2 | get_bits(opcode, 7, 6)

            # if d IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "ASR", setflags, condition, operands, encoding, ".W")            

        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            imm5 = get_bits(opcode, 11, 7)
            _, imm5 = DecodeImmShift(0b10, imm5)

            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 15 and setflags:
                return self.decode_subs_pc_lr_arm(opcode, encoding)            

            operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            ins = Instruction(ins_id, opcode, "ASR", setflags, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
        
    def decode_ror_immediate(self, opcode, encoding):
        """
        A8.8.149
        ROR (immediate)
        Rotate Right (immediate) provides the value of the contents of a register rotated by a constant value. The bits that
        are rotated off the right end are inserted into the vacated bit positions on the left. It can optionally update the
        condition flags based on the result.
        
        Syntax:
        ROR{S}{<c>}{<q>} {<Rd>,} <Rm>, #<imm>
        """
        props = {}
        ins_id = ARMInstruction.ror_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
                
            imm5 = get_bits(opcode, 14, 12) << 2 | get_bits(opcode, 7, 6)
            
            # if (imm3:imm2) == '00000' then SEE RRX;
            if imm5 == 0:
                return self.decode_rrx(opcode, encoding)
            
            # if d IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            setflags = get_bit(opcode, 20)
            imm5 = get_bits(opcode, 11, 7) 
             
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 15 and setflags:
                return self.decode_subs_pc_lr_arm(opcode, encoding)

            # if imm5 == '00000' then SEE RRX;
            if imm5 == 0:
                return self.decode_rrx(opcode, encoding)            

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rm), Immediate(imm5)]
        ins = Instruction(ins_id, opcode, "ROR", setflags, condition, operands, encoding)
        return ins
        
    def decode_bic_immediate(self, opcode, encoding):
        """
        A8.8.21
        BIC (immediate)
        Bitwise Bit Clear (immediate) performs a bitwise AND of a register value and the complement of an immediate
        value, and writes the result to the destination register. It can optionally update the condition flags based on the result.
        
        Syntax:
        BIC{S}{<c>}{<q>} {<Rd>,} <Rn>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.bic_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
                        
            imm32, _ = ThumbExpandImm_C(opcode, 0)
            
            # if d IN {13,15} || n IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd) or BadReg(Rn):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            Rn = get_bits(opcode, 19, 16)
            setflags = get_bit(opcode, 20)
                        
            imm32, _ = ARMExpandImm_C(opcode, 0)
 
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 15 and setflags:
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "BIC", setflags, condition, operands, encoding)            
        
        return ins
        
    def decode_mvn_immediate(self, opcode, encoding):
        """
        A8.8.115
        MVN (immediate)
        Bitwise NOT (immediate) writes the bitwise inverse of an immediate value to the destination register. It can
        optionally update the condition flags based on the value.

        Syntax:
        MVN{S}{<c>}{<q>} <Rd>, #<const>
        """
        props = {}
        ins_id = ARMInstruction.mvn_immediate
        condition = self.decode_condition_field(opcode)
        
        qualifiers = ""
        if encoding == eEncodingT1:
            Rd = get_bits(opcode, 11, 8)
            setflags = get_bit(opcode, 20)
                        
            imm32, _ = ThumbExpandImm_C(opcode, 0)
            
            # if d IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd):
                raise UnpredictableInstructionException()
            
            condition = None
            qualifiers = ".W"
            
        elif encoding == eEncodingA1:
            Rd = get_bits(opcode, 15, 12)
            setflags = get_bit(opcode, 20)
                        
            imm32, _ = ARMExpandImm_C(opcode, 0)
 
            # if Rd == '1111' && S == '1' then SEE SUBS PC, LR and related instructions;
            if Rd == 15 and setflags:
                return self.decode_subs_pc_lr_arm(opcode, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [Register(Rd), Immediate(imm32)]
        ins = Instruction(ins_id, opcode, "MVN", setflags, condition, operands, encoding, qualifiers)
        return ins

    def decode_str_immediate_thumb(self, opcode, encoding):
        """
        A8.8.203
        STR (immediate, Thumb)
        Store Register (immediate) calculates an address from a base register value and an immediate offset, and stores a
        word from a register to memory. It can use offset, post-indexed, or pre-indexed addressing.        
        """
        props = {}
        ins_id = ARMInstruction.str_immediate
        if encoding == eEncodingT1:
            # imm32 = ZeroExtend(imm5:'00', 32);
            imm32 = get_bits(opcode, 10, 6) << 2
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            
            index = True
            add = True
            wback = False

            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "STR", False, None, operands, encoding)
        
        elif encoding == eEncodingT2:
            # imm32 = ZeroExtend(imm5:'00', 32);
            imm32 = get_bits(opcode, 7, 0) << 2
            Rt = get_bits(opcode, 10, 8)
            
            index = True
            add = True
            wback = False

            operands = [Register(Rt), Memory(ARMRegister.SP, Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "STR", False, None, operands, encoding)
        
        elif encoding == eEncodingT3:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)

            index = True
            add = True
            wback = False
            
            # if Rn == '1111' then UNDEFINED;
            if Rt == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "STR", False, None, operands, encoding, ".W")
        
        elif encoding == eEncodingT4:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            P = get_bit(opcode, 10)
            U = get_bit(opcode, 9)
            W = get_bit(opcode, 8)
            imm32 = get_bits(opcode, 7, 0)
            
            # if P == '1' && U == '1' && W == '0' then SEE STRT;
            if P == 1 and U == 1 and W == 0:
                return self.decode_strt(opcode, encoding)
            
            # if Rn == '1101' && P == '1' && U == '0' && W == '1' && imm8 == '00000100' then SEE PUSH;
            if Rn == 0b1101 and P == 1 and U == 0 and W == 1 and imm32 == 0b100:
                return self.decode_push(opcode, encoding)
            
            # if Rn == '1111' || (P == '0' && W == '0') then UNDEFINED;
            if Rn == 0b1111 or (P == 0 and W == 0):
                raise UndefinedOpcode()
            
            index = P == 1
            add = U == 1
            wback = W == 1
            
            # if t == 15 || (wback && n == t) then UNPREDICTABLE;
            if Rt == 15 or (wback and Rn == Rt):
                raise UnpredictableInstructionException()

            if not add:
                imm32 *= -1
                
            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
                ins = Instruction(ins_id, opcode, "STR", False, None, operands, encoding)
        
            elif index == True and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=True)]
                ins = Instruction(ins_id, opcode, "STR", False, None, operands, encoding)
        
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
                ins = Instruction(ins_id, opcode, "STR", False, None, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                
        return ins

    def decode_str_immediate_arm(self, opcode, encoding):
        """
        A8.8.204
        STR (immediate, ARM)
        Store Register (immediate) calculates an address from a base register value and an immediate offset, and stores a
        word from a register to memory. It can use offset, post-indexed, or pre-indexed addressing.
                
        Syntax:
        STR{<c>}{<q>} <Rt>, [<Rn> {, #+/-<imm>}]  Offset: index==TRUE, wback==FALSE
        STR{<c>}{<q>} <Rt>, [<Rn>, #+/-<imm>]!    Pre-indexed: index==TRUE, wback==TRUE
        STR{<c>}{<q>} <Rt>, [<Rn>], #+/-<imm>     Post-indexed: index==FALSE, wback==TRUE
        """
        props = {}
        ins_id = ARMInstruction.str_immediate
        condition = self.decode_condition_field(opcode)
        
        P = get_bit(opcode, 24)
        U = get_bit(opcode, 23)
        W = get_bit(opcode, 21)
        Rn = get_bits(opcode, 19, 16)
        Rt = get_bits(opcode, 15, 12)
        imm12 = get_bits(opcode, 11, 0)
        
        # if P == '0' && W == '1' then SEE STRT;
        if P == 0 and W == 1:
            return self.decode_strt(opcode, encoding)
        
        # if Rn == '1101' && P == '1' && U == '0' && W == '1' && imm12 == '000000000100' then SEE PUSH;
        if Rn == 0b1101 and P == 1 and U == 0 and W == 1 and imm12 == 0b100:
            return self.decode_push(opcode, encoding)
        
        index = P == 1
        add = U == 1
        wback = P == 0 or W == 1
        
        # if wback && (n == 15 || n == t) then UNPREDICTABLE;
        if wback and (Rn == 15 or Rn == Rt):
            raise UnpredictableInstructionException()
                
        if not add:
            imm12 *= -1
        
        if index == True and wback == False:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm12), wback=False)]
            ins = Instruction(ins_id, opcode, "STR", False, condition, operands, encoding)
        
        elif index == True and wback == True:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm12), wback=True)]
            ins = Instruction(ins_id, opcode, "STR", False, condition, operands, encoding)
        
        elif index == False and wback == True:
            operands = [Register(Rt), Memory(Register(Rn), wback=False), Immediate(imm12)]
            ins = Instruction(ins_id, opcode, "STR", False, condition, operands, encoding)
            
        return ins
        

    def decode_str_reg(self, opcode, encoding):
        """
        A8.8.205
        STR (register)
        Store Register (register) calculates an address from a base register value and an offset register value, stores a word
        from a register to memory. The offset register value can optionally be shifted
        
        Syntax:
        STR{<c>}{<q>} <Rt>, [<Rn>, <Rm>{, <shift>}]   Offset: index==TRUE, wback==FALSE
        STR{<c>}{<q>} <Rt>, [<Rn>, <Rm>{, <shift>}]!  Pre-indexed: index==TRUE, wback==TRUE
        STR{<c>}{<q>} <Rt>, [<Rn>], <Rm>{, <shift>}   Post-indexed: index==FALSE, wback==TRUE
        """
        props = {}
        ins_id = ARMInstruction.str_reg
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 8, 6)
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            
            index = True
            add = True
            wback = False
            
            shift_t = SRType_LSL
            shift_n = 0
            
            # TODO:
            # if CurrentInstrSet() == InstrSet_ThumbEE then SEE "Modified operation in ThumbEE";
            
            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm))]
            ins = Instruction(ins_id, opcode, "STR", False, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm2 = get_bits(opcode, 5, 4)
            Rm = get_bits(opcode, 3, 0)
        
            # if Rn == '1111' then UNDEFINED;
            if Rn == 0b1111:
                raise UnpredictableInstructionException()
            
            # if t == 15 || m IN {13,15} then UNPREDICTABLE;
            if Rt == 15 or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            index = True
            add = True
            wback = False
            
            shift_t = SRType_LSL
            shift_n = imm2

            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n))]
            ins = Instruction(ins_id, opcode, "STR", False, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm5 = get_bits(opcode, 11, 7)
            type_ = get_bits(opcode, 6, 5)
            Rm = get_bits(opcode, 3, 0)
            
            # if P == '0' && W == '1' then SEE STRT;
            if P == 0 and W == 1:
                # NOTE: Encoding changed to match other disassemblers.
                encoding = eEncodingA2
                return self.decode_strt(opcode, encoding)
            
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            shift_t, shift_n = DecodeImmShift(type_, imm5)
            
            # if m == 15 then UNPREDICTABLE;
            if Rm == 15:
                raise UnpredictableInstructionException()
            
            # if wback && (n == 15 || n == t) then UNPREDICTABLE;
            if wback and (Rn == 15 or Rn == Rt):
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and wback and Rm == Rn:
                raise UnpredictableInstructionException()

            
            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, add == False), RegisterShift(shift_t, shift_n), wback=False)]
                ins = Instruction(ins_id, opcode, "STR", False, condition, operands, encoding)
            
            elif index == True and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, add == False), RegisterShift(shift_t, shift_n), wback=True)]
                ins = Instruction(ins_id, opcode, "STR", False, condition, operands, encoding)
            
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, add == False), RegisterShift(shift_t, shift_n)]
                ins = Instruction(ins_id, opcode, "STR", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                
        return ins

    def decode_strh_immediate_arm(self, opcode, encoding):
        """
        A8.8.217
        STRH (immediate, ARM)
        Store Register Halfword (immediate) calculates an address from a base register value and an immediate offset, and
        stores a halfword from a register to memory. It can use offset, post-indexed, or pre-indexed addressing.         
        """
        props = {}
        ins_id = ARMInstruction.strh_immediate_arm
        condition = self.decode_condition_field(opcode)
        
        P = get_bit(opcode, 24)
        U = get_bit(opcode, 23)
        W = get_bit(opcode, 21)
        Rn = get_bits(opcode, 19, 16)
        Rt = get_bits(opcode, 15, 12)
        imm4H = get_bits(opcode, 11, 8)
        imm4L = get_bits(opcode, 3, 0)
        
        # if P == '0' && W == '1' then SEE STRHT;
        if P == 0 and W == 1:
            raise RuntimeError("SEE STRHT")
        
        # t = UInt(Rt); n = UInt(Rn); imm32 = ZeroExtend(imm4H:imm4L, 32);
        imm32 = (imm4H << 4) | imm4L
        
        # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
        index = P == 1
        add = U == 1
        wback = P == 0 or W == 1
        
        if not add:
            imm32 *= -1
        
        if Rt == 15:
            raise UnpredictableInstructionException()
        
        if wback and (Rn == 15 or Rn == Rt):
            raise UnpredictableInstructionException()
        
        if index == True and wback == False:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
        
        elif index == True and wback == True:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=True)]
            
        else:
            operands = [Register(Rt), Memory(Register(Rn), wback=True), Immediate(imm32)]
            
        return Instruction(ins_id, opcode, "STRH", False, condition, operands, encoding)
    
    def decode_strt(self, opcode, encoding):
        """
        A8.8.220
        STRT
        Store Register Unprivileged stores a word from a register to memory.
        
        Syntax:
        STRT{<c>}{<q>} <Rt>, [<Rn> {, #<imm>}]           Offset: Thumb only
        STRT{<c>}{<q>} <Rt>, [<Rn>] {, #+/-<imm>}        Post-indexed: ARM only
        STRT{<c>}{<q>} <Rt>, [<Rn>], +/-<Rm> {, <shift>} Post-indexed: ARM only         
        """
        props = {}
        ins_id = ARMInstruction.strt
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 7, 0)
            
            # if Rn == '1111' then UNDEFINED;
            if Rn == 0b1111:
                raise UnpredictableInstructionException()
            
            postindex = False
            add = True
            register_form = False
            
            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "STRT", False, condition, operands, encoding)
            
        elif encoding == eEncodingA1:
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            add = U == 1
            register_form = False
            
            # if n == 15 || n == t then UNPREDICTABLE;
            if Rn == 15 or Rn == Rt:
                raise UnpredictableInstructionException()
            
            if not add:
                imm32 *= -1

            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "STRT", False, condition, operands, encoding)
        
        elif encoding == eEncodingA2:
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm5 = get_bits(opcode, 11, 7)
            type_ = get_bits(opcode, 6, 5)
            Rm = get_bits(opcode, 3, 0)
            
            post_index = True
            add = U == 1
            register_form = True
            
            shift_t, shift_n = DecodeImmShift(type_, imm5)
            
            # if n == 15 || n == t || m == 15 then UNPREDICTABLE;
            if Rn == 15 or Rn == Rt or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and Rm == Rn:
                raise UnpredictableInstructionException()
            
            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, not add), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "STRT", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
    
    def decode_ldr_immediate_thumb(self, opcode, encoding):
        """
        A8.8.62
        LDR (immediate, Thumb)
        Load Register (immediate) calculates an address from a base register value and an immediate offset, loads a word
        from memory, and writes it to a register. It can use offset, post-indexed, or pre-indexed addressing. 
        """
        props = {}
        ins_id = ARMInstruction.ldr_immediate
        if encoding == eEncodingT1:
            # imm32 = ZeroExtend(imm5:'00', 32);
            imm32 = get_bits(opcode, 10, 6) << 2
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            
            index = True
            add = True
            wback = False

            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDR", False, None, operands, encoding)
        
        elif encoding == eEncodingT2:
            # imm32 = ZeroExtend(imm5:'00', 32);
            imm32 = get_bits(opcode, 7, 0) << 2
            Rt = get_bits(opcode, 10, 8)
            
            index = True
            add = True
            wback = False

            operands = [Register(Rt), Memory(ARMRegister.SP, Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDR", False, None, operands, encoding)
        
        elif encoding == eEncodingT3:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)

            index = True
            add = True
            wback = False
            
            # if Rn == '1111' then UNDEFINED;
            if Rn == 0b1111:
                return self.decode_ldr_literal(opcode, eEncodingT2)
            
            # if t == 15 && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if Rt == 15 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDR", False, None, operands, encoding, ".W")
        
        elif encoding == eEncodingT4:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            P = get_bit(opcode, 10)
            U = get_bit(opcode, 9)
            W = get_bit(opcode, 8)
            imm32 = get_bits(opcode, 7, 0)
            
            # if Rn == '1111' then SEE LDR (literal);
            if Rn == 0b1111:
                return self.decode_ldr_literal(opcode, encoding)

            # if P == '1' && U == '1' && W == '0' then SEE STRT;
            if P == 1 and U == 1 and W == 0:
                return self.decode_ldrt(opcode, encoding)
            
            # if Rn == '1101' && P == '0' && U == '1' && W == '1' && imm8 == '00000100' then SEE POP;
            if Rn == 0b1101 and P == 0 and U == 1 and W == 1 and imm32 == 0b100:
                return self.decode_pop_thumb(opcode, encoding)
            
            # if P == '0' && W == '0' then UNDEFINED;
            if P == 0 and W == 0:
                raise UndefinedOpcode()
            
            index = P == 1
            add = U == 1
            wback = W == 1
            
            # if (wback && n == t) || (t == 15 && InITBlock() && !LastInITBlock()) then UNPREDICTABLE;
            if (wback and Rn == Rt) or (Rt == 15 and self.InITBlock() and not self.LastInITBlock()):
                raise UnpredictableInstructionException()

            if not add:
                imm32 *= -1
                
            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
                ins = Instruction(ins_id, opcode, "LDR", False, None, operands, encoding)
        
            elif index == True and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=True)]
                ins = Instruction(ins_id, opcode, "STR", False, None, operands, encoding)
        
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), wback=True), Immediate(imm32)]
                ins = Instruction(ins_id, opcode, "STR", False, None, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                
        return ins
    
    def decode_ldrh_immediate_thumb(self, opcode, encoding):
        """
        A8.8.79
        LDRH (immediate, Thumb)
        Load Register Halfword (immediate) calculates an address from a base register
        value and an immediate offset, loads a halfword from memory, zero-extends it 
        to form a 32-bit word, and writes it to a register. It can use offset,
        post-indexed, or pre-indexed addressing        
        """
        props = {}
        ins_id = ARMInstruction.ldrh_immediate_thumb
        if encoding == eEncodingT1:
            # imm32 = ZeroExtend(imm5:'0', 32);
            imm32 = get_bits(opcode, 10, 6) << 1
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            index = True
            add = True
            wback = False
            
            # LDRH<c> <Rt>, [<Rn>{, #<imm>}]
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDRH", False, None, operands, encoding)
        
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            index = True
            add = True
            wback = False
            
            # if Rt == '1111' then SEE "Related instructions";
            if Rt == 0b1111:
                raise RuntimeError("SEE Related instructions")
            
            # if Rn == '1111' then SEE LDRH (literal);
            if Rn == 0b1111:
                return self.decode_ldrh_literal_thumb(opcode, eEncodingT1)
            
            index = True
            add = True
            wback = False

            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()
            
            # LDRH<c>.W <Rt>, [<Rn>{, #<imm12>}]
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDRH", False, None, operands, encoding, ".W")
        
        elif encoding == eEncodingT3:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 7, 0)
            P = get_bit(opcode, 10)
            U = get_bit(opcode, 9)
            W = get_bit(opcode, 8)

            # if Rn == '1111' then SEE LDRH (literal);
            if Rn == 0b1111:
                return self.decode_ldrh_literal_thumb(opcode, eEncodingT1)
            
            # if Rt == '1111' && P == '1' && U == '0' && W == '0' then SEE "Related instructions";
            if Rt == 0b1111 and P == 1 and U == 0 and W == 0:
                raise RuntimeError("SEE Related instructions")
                
            # if P == '1' && U == '1' && W == '0' then SEE LDRHT;
            if P == 1 and U == 1 and W == 0:
                raise RuntimeError("SEE LDRHT")
            
            # if P == '0' && W == '0' then UNDEFINED;
            if P == 0 and W == 0:
                raise UndefinedOpcode()
            
            # index = (P == '1'); add = (U == '1'); wback = (W == '1');
            index = P == 1
            add = U == 1
            wback = W == 1

            # if t ==13 || (t ==15 && W == '1') || (wback && n == t) then UNPREDICTABLE;
            if Rt == 14 or (Rt == 15 and W == 1) or (wback and Rn == Rt):
                raise UnpredictableInstructionException()

            # LDRH{<c>}{<q>} <Rt>, [<Rn> {, #+/-<imm>}]    Offset: index==TRUE, wback==FALSE
            # LDRH{<c>}{<q>} <Rt>, [<Rn>, #+/-<imm>]!      Pre-indexed: index==TRUE, wback==TRUE
            # LDRH{<c>}{<q>} <Rt>, [<Rn>], #+/-<imm>       Post-indexed: index==FALSE, wback==TRUE
            if not add:
                imm32 *= -1
                
            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
                ins = Instruction(ins_id, opcode, "LDRH", False, None, operands, encoding)
        
            elif index == True and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=True)]
                ins = Instruction(ins_id, opcode, "LDRH", False, None, operands, encoding)
        
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
                ins = Instruction(ins_id, opcode, "LDRH", False, None, operands, encoding)
                
        return ins

    def decode_ldrh_immediate_arm(self, opcode, encoding):
        """
        A8.8.80
        LDRH (immediate, ARM)
        Load Register Halfword (immediate) calculates an address from a base register value
        and an immediate offset, loads a halfword from memory, zero-extends it to form a
        32-bit word, and writes it to a register. It can use offset, post-indexed, or pre-indexed
        addressing        
        """
        props = {}
        ins_id = ARMInstruction.ldrh_immediate_arm
        if encoding == eEncodingA1:
            cond = self.decode_condition_field(opcode)
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            W = get_bit(opcode, 21)
            
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            
            imm4H = get_bits(opcode, 11, 8)
            imm4L = get_bits(opcode, 3, 0)
            
            # if Rn == '1111' then SEE LDRH (literal);
            if Rn == 0b1111:
                return self.decode_ldrh_literal_arm(opcode, encoding)
            
            # if P == '0' && W == '1' then SEE LDRHT;
            if P == 0 and W == 1:
                # TODO: Implement
                raise RuntimeError("Implement LDRHT")
            
            # t = UInt(Rt); n = UInt(Rn); imm32 = ZeroExtend(imm4H:imm4L, 32);
            imm32 = (imm4H << 4) | imm4L 
            
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1
            add = U == 1 
            wback = (P == 0) or (W == 1)
            
            if not add:
                imm32 *= -1
            
            # if t == 15 || (wback && n == t) then UNPREDICTABLE;
            if Rt == 15 or (wback and Rn == Rt):
                raise UnpredictableInstructionException()

            # LDRH{<c>}{<q>} <Rt>, [<Rn> {, #+/-<imm>}] Offset: index==TRUE, wback==FALSE
            # LDRH{<c>}{<q>} <Rt>, [<Rn>, #+/-<imm>]!   Pre-indexed: index==TRUE, wback==TRUE
            # LDRH{<c>}{<q>} <Rt>, [<Rn>], #+/-<imm>    Post-indexed: index==FALSE, wback==TRUE
            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), None, Immediate(imm32), wback)]
                ins = Instruction(ins_id, opcode, "LDRH", False, cond, operands, encoding)            
                
            elif index == True and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), None, Immediate(imm32), wback)]
                ins = Instruction(ins_id, opcode, "LDRH", False, cond, operands, encoding)            
    
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), None, None, wback), Immediate(imm32)]
                ins = Instruction(ins_id, opcode, "LDRH", False, cond, operands, encoding)
        
        return ins
    
    def decode_ldrh_literal_thumb(self, opcode, encoding):
        """
        A8.8.81
        LDRH (literal)
        Load Register Halfword (literal) calculates an address from the PC value 
        and an immediate offset, loads a halfword from memory, zero-extends it to form a
        32-bit word, and writes it to a register.        
        """
        props = {}        
        ins_id = ARMInstruction.ldrh_literal_thumb
        if encoding == eEncodingT1:
            U = get_bit(opcode, 23)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            
            # if Rt == '1111' then SEE "Related instructions";
            if Rt == 0b1111:
                raise RuntimeError("SEE Related instructions")
            
            # t = UInt(Rt); imm32 = ZeroExtend(imm12, 32); add = (U == '1');
            add = U == 1
            if not add:
                imm32 *= -1
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()
            
            condition = None            
            operands = [Register(Rt), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "LDRH", False, condition, operands, encoding)            
        
        return ins
    
    def decode_ldrh_literal_arm(self, opcode, encoding):
        """
        A8.8.81
        LDRH (literal)
        Load Register Halfword (literal) calculates an address from the PC value 
        and an immediate offset, loads a halfword from memory, zero-extends it to form a
        32-bit word, and writes it to a register.        
        """
        props = {}
        ins_id = ARMInstruction.ldrh_literal_arm
        if encoding == eEncodingA1:
            condition = self.decode_condition_field(opcode)
            
            U = get_bit(opcode, 23)
            Rt = get_bits(opcode, 15, 12)
            imm4H = get_bits(opcode, 11, 8)
            imm4L = get_bits(opcode, 3, 0)
            
            # t = UInt(Rt); imm32 = ZeroExtend(imm4H:imm4L, 32);
            imm32 = (imm4H << 4) | imm4L
            add = U == 1
            
            # if t == 15 then UNPREDICTABLE;
            if Rt == 15:
                raise UnpredictableInstructionException()

            if not add:
                imm32 *= -1

            operands = [Register(Rt), Memory(Register(ARMRegister.PC), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDRH", False, condition, operands, encoding)
            
        return ins

    def decode_ldrh_register_thumb(self, opcode, encoding):
        """
        A8.8.82
        LDRH (register)
        Load Register Halfword (register) calculates an address from a base register
        value and an offset register value, loads a halfword from memory, zero-extends it 
        to form a 32-bit word, and writes it to a register. The offset register value
        can be shifted left by 0, 1, 2, or 3 bits.         
        """
        props = {}
        ins_id = ARMInstruction.ldrh_register_thumb
        if encoding == eEncodingT1:
            # if CurrentInstrSet() == InstrSet_ThumbEE then SEE "Modified operation in ThumbEE";    
            Rm = get_bits(opcode, 8, 6)
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            
            # LDRH<c> <Rt>, [<Rn>, <Rm>]
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm))]
            ins = Instruction(ins_id, opcode, "LDRH", False, None, operands, encoding)
        
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            imm2 = get_bits(opcode, 5, 4)
            
            # if Rn == '1111' then SEE LDRH (literal);
            if Rn == 0b1111:
                return self.decode_ldrh_literal_thumb(opcode, eEncodingT1)
            
            # if Rt == '1111' then SEE "Related instructions";
            if Rt == 0b1111:
                raise RuntimeError("SEE Related instructions")
            
            index = True
            add = True
            wback = False            
            shift_t, shift_n = SRType_LSL, imm2

            # if t == 13 || m IN {13,15} then UNPREDICTABLE;
            if Rt == 13 or Rm in [13, 15]:
                raise UnpredictableInstructionException()

            # LDRH<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}]
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n))]
            ins = Instruction(ins_id, opcode, "LDRH", False, None, operands, encoding, ".W")

        return ins
            
    def decode_ldrh_register_arm(self, opcode, encoding):
        """
        A8.8.82
        LDRH (register)
        Load Register Halfword (register) calculates an address from a base register
        value and an offset register value, loads a halfword from memory, zero-extends it 
        to form a 32-bit word, and writes it to a register. The offset register value
        can be shifted left by 0, 1, 2, or 3 bits.         
        """
        props = {}
        ins_id = ARMInstruction.ldrh_register_arm
        if encoding == eEncodingA1:
            condition = self.decode_condition_field(opcode)
            
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            Rm = get_bits(opcode, 3, 0)
            
            # if P == '0' && W == '1' then SEE LDRHT;
            if P == 0 and W == 1:
                raise RuntimeError("SEE LDRHT")
            
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1
            add = U == 1
            wback = (P == 0) or (W == 1)

            # if t == 15 || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if wback && (n == 15 || n == t) then UNPREDICTABLE;
            if wback and (Rn == 15 or Rn == Rt):
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and wback and Rm == Rn:
                raise UnpredictableInstructionException()

            if index == True and wback == False:
                # LDRH{<c>}{<q>} <Rt>, [<Rn>, <Rm>{, LSL #<imm>}]
                operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, not add))]
                ins = Instruction(ins_id, opcode, "LDRH", False, condition, operands, encoding)
            
            elif index == True and wback == True:
                # LDRH{<c>}{<q>} <Rt>, [<Rn>, +/-<Rm>]!
                operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, not add), wback=wback)]
                ins = Instruction(ins_id, opcode, "LDRH", False, condition, operands, encoding)
            
            elif index == False and wback == True:
                # LDRH{<c>}{<q>} <Rt>, [<Rn>], +/-<Rm>
                operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, not add)]
                ins = Instruction(ins_id, opcode, "LDRH", False, condition, operands, encoding)

        return ins
    
    def decode_ldr_immediate_arm(self, opcode, encoding):
        """
        A8.8.63
        LDR (immediate, ARM)
        Load Register (immediate) calculates an address from a base register value and an immediate offset, loads a word
        from memory, and writes it to a register. It can use offset, post-indexed, or pre-indexed addressing.
        
        Syntax:
        LDR{<c>}{<q>} <Rt>, [<Rn> {, #+/-<imm>}]  Offset: index==TRUE, wback==FALSE
        LDR{<c>}{<q>} <Rt>, [<Rn>, #+/-<imm>]!    Pre-indexed: index==TRUE, wback==TRUE
        LDR{<c>}{<q>} <Rt>, [<Rn>], #+/-<imm>     Post-indexed: index==FALSE, wback==TRUE
        """
        props = {}
        ins_id = ARMInstruction.ldr_immediate
        condition = self.decode_condition_field(opcode)
        
        P = get_bit(opcode, 24)
        U = get_bit(opcode, 23)
        W = get_bit(opcode, 21)
        Rn = get_bits(opcode, 19, 16)
        Rt = get_bits(opcode, 15, 12)
        imm12 = get_bits(opcode, 11, 0)
        
        # if Rn == '1111' then SEE LDR (literal);
        if Rn == 0b1111:
            return self.decode_ldr_literal(opcode, encoding)
        
        # if P == '0' && W == '1' then SEE LDRT;
        if P == 0 and W == 1:
            return self.decode_ldrt(opcode, encoding)
        
        # if Rn == '1101' && P == '0' && U == '1' && W == '0' && imm12 == '000000000100' then SEE POP;
        if Rn == 0b1101 and P == 0 and U == 1 and W == 0 and imm12 == 0b100:
            # NOTE: Changed the encoding
            encoding = eEncodingA2
            return self.decode_pop_arm(opcode, encoding)
        
        index = P == 1
        add = U == 1
        wback = P == 0 or W == 1
        
        if not add:
            imm12 *= -1
        
        # if wback && n == t then UNPREDICTABLE;
        if wback == True and Rn == Rt:
            raise UnpredictableInstructionException()
        
        if index == True and wback == False:
            operands = [Register(Rt), Memory(Register(Rn), None, Immediate(imm12), wback)]
            ins = Instruction(ins_id, opcode, "LDR", False, condition, operands, encoding)            
            
        elif index == True and wback == True:
            operands = [Register(Rt), Memory(Register(Rn), None, Immediate(imm12), wback)]
            ins = Instruction(ins_id, opcode, "LDR", False, condition, operands, encoding)            

        elif index == False and wback == True:
            operands = [Register(Rt), Memory(Register(Rn), None, None, wback), Immediate(imm12)]
            ins = Instruction(ins_id, opcode, "LDR", False, condition, operands, encoding)

        return ins
    
    def decode_ldr_literal(self, opcode, encoding):
        """
        A8.8.64
        LDR (literal)
        Load Register (literal) calculates an address from the PC value and an immediate offset, loads a word from memory,
        and writes it to a register.        
        
        Syntax:
        LDR{<c>}{<q>} <Rt>, <label>         Normal form
        LDR{<c>}{<q>} <Rt>, [PC, #+/-<imm>] Alternative form        
        """
        props = {}
        ins_id = ARMInstruction.ldr_literal
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rt = get_bits(opcode, 10, 8)
            imm32 = get_bits(opcode, 7, 0) << 2
            add = True

            condition = None            
            operands = [Register(Rt), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "LDR", False, condition, operands, encoding)            

        elif encoding == eEncodingT2:
            U = get_bit(opcode, 23)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            add = U == 1
            
            # if t == 15 && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if Rt == 15 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            if not add:
                imm32 *= -1

            condition = None
            operands = [Register(Rt), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "LDR", False, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            U = get_bit(opcode, 23)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            add = U == 1

            if not add:
                imm32 *= -1

            operands = [Register(Rt), Memory(ARMRegister.PC, Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDR", False, condition, operands, encoding)            

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                
        return ins
    
    def decode_ldr_register_thumb(self, opcode, encoding):
        """
        A8.8.65
        LDR (register, Thumb)
        Load Register (register) calculates an address from a base register value and an offset register value, loads a word
        from memory, and writes it to a register. The offset register value can optionally be shifted.         
        """
        props = {}
        ins_id = ARMInstruction.ldr_register
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 8, 6)
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
        
            # TODO:
            # if CurrentInstrSet() == InstrSet_ThumbEE then SEE "Modified operation in ThumbEE";
            
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm))]
            ins = Instruction(ins_id, opcode, "LDR", False, None, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm2 = get_bits(opcode, 5, 4)
            Rm = get_bits(opcode, 3, 0)
            
            # if Rn == '1111' then SEE LDR (literal);
            if Rn == 0b111:
                return self.decode_ldr_literal(opcode, encoding)
        
            shift_t, shift_n = SRType_LSL, imm2
            
            # if m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rm):
                raise UnpredictableInstructionException()
    
            # if t == 15 && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if Rt == 15 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
    
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n))]
            ins = Instruction(ins_id, opcode, "LDR", False, None, operands, encoding, ".W")
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        return ins
    
    def decode_ldr_register_arm(self, opcode, encoding):
        """
        A8.8.66
        LDR (register, ARM)
        Load Register (register) calculates an address from a base register value and an offset register value, loads a word
        from memory, and writes it to a register. The offset register value can optionally be shifted.      

        Syntax:
        LDR{<c>}{<q>} <Rt>, [<Rn>, {+/-}<Rm>{, <shift>}]  Offset: index==TRUE, wback==FALSE
        LDR{<c>}{<q>} <Rt>, [<Rn>, {+/-}<Rm>{, <shift>}]! Pre-indexed: index==TRUE, wback==TRUE
        LDR{<c>}{<q>} <Rt>, [<Rn>], {+/-}<Rm>{, <shift>}  Post-indexed: index==FALSE, wback==TRUE        
        """
        props = {}
        ins_id = ARMInstruction.ldr_register
        condition = self.decode_condition_field(opcode)
        
        P = get_bit(opcode, 24)
        U = get_bit(opcode, 23)
        W = get_bit(opcode, 21)
        Rn = get_bits(opcode, 19, 16)
        Rt = get_bits(opcode, 15, 12)
        imm5 = get_bits(opcode, 11, 7)
        type_ = get_bits(opcode, 6, 5)
        Rm = get_bits(opcode, 3, 0)
        
        if P == 0 and W == 1:
            # NOTE: Encoding changed to match other disassemblers.
            encoding = eEncodingA2
            return self.decode_ldrt(opcode, encoding)
        
        index = P == 1
        add = U == 1
        wback = P == 0 or W == 1
        
        shift_t, shift_n = DecodeImmShift(type_, imm5)
        
        # if P == '0' && W == '1' then SEE LDRT;
        if P == 0 and W == 1:
            # NOTE: Encoding changed to match other disassemblers.
            encoding = eEncodingA2            
            return self.decode_ldrt(opcode, encoding)
        
        # if m == 15 then UNPREDICTABLE;
        if Rm == 15:
            raise UnpredictableInstructionException()
        
        # if wback && (n == 15 || n == t) then UNPREDICTABLE;
        if wback and (Rn == 15 or Rn == Rt):
            raise UnpredictableInstructionException()
        
        # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
        if self.ArchVersion() < 16 and wback and Rm == Rn:
            raise UnpredictableInstructionException()
        
        # LDR{<c>}{<q>} <Rt>, [<Rn> , {+/-}<Rm> {, <shift>}]
        # LDR{<c>}{<q>} <Rt>, [<Rn> , {+/-}<Rm> {, <shift>}]!
        # LDR{<c>}{<q>} <Rt>, [<Rn>], {+/-}<Rm> {, <shift>}
        
        if index == True:
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, not add), RegisterShift(shift_t, shift_n), wback)]
                
        elif index == False:
            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, not add), RegisterShift(shift_t, shift_n)]
            
        ins = Instruction(ins_id, opcode, "LDR", False, condition, operands, encoding)
        return ins
    
    def decode_ldrt(self, opcode, encoding):
        """
        A8.8.92
        LDRT
        Load Register Unprivileged loads a word from memory, and writes it to a register.
        
        Syntax:
        LDRT{<c>}{<q>} <Rt>, [<Rn> {, #<imm>}]            Offset: Thumb only
        LDRT{<c>}{<q>} <Rt>, [<Rn>] {, #+/-<imm>}         Post-indexed: ARM only
        LDRT{<c>}{<q>} <Rt>, [<Rn>], +/-<Rm> {, <shift>}  Post-indexed: ARM only
        """
        props = {}
        ins_id = ARMInstruction.ldrt
        condition = self.decode_condition_field(opcode)
                
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 7, 0)
            
            # if Rn == '1111' then SEE LDR (literal);
            if Rn == 0b1111:
                return self.decode_ldr_literal(opcode, encoding)
            
            postindex = False
            add = True
            register_form = False
            
            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDRT", False, condition, operands, encoding)
            
        elif encoding == eEncodingA1:
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            add = U == 1
            register_form = False
            post_index = True
            
            # if t == 15 || n == 15 || n == t then UNPREDICTABLE;
            if Rn == 15 or Rt == 15 or Rn == Rt:
                raise UnpredictableInstructionException()
            
            if not add:
                imm32 *= -1

            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "LDRT", False, condition, operands, encoding)
        
        elif encoding == eEncodingA2:
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm5 = get_bits(opcode, 11, 7)
            type_ = get_bits(opcode, 6, 5)
            Rm = get_bits(opcode, 3, 0)
            
            post_index = True
            add = U == 1
            register_form = True
            
            shift_t, shift_n = DecodeImmShift(type_, imm5)
            
            # if t == 15 || n == 15 || n == t || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and Rm == Rn:
                raise UnpredictableInstructionException()

            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, not add), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "LDRT", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                
        return ins
    
    def decode_strb_register(self, opcode, encoding):
        """
        A8.8.208
        STRB (register)
        Store Register Byte (register) calculates an address from a base register value and an offset register value, and stores
        a byte from a register to memory. The offset register value can optionally be shifted.        
        
        Syntax:
        STRB{<c>}{<q>} <Rt>, [<Rn>, <Rm>{, <shift>}]   Offset: index==TRUE, wback==FALSE
        STRB{<c>}{<q>} <Rt>, [<Rn>, <Rm>{, <shift>}]!  Pre-indexed: index==TRUE, wback==TRUE
        STRB{<c>}{<q>} <Rt>, [<Rn>], <Rm>{, <shift>}   Post-indexed: index==FALSE, wback==TRUE
        """
        props = {}
        ins_id = ARMInstruction.strb_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 8, 6)
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            
            index = True
            add = True
            wback = False
            
            shift_t = SRType_LSL
            shift_n = 0
            
            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm))]
            ins = Instruction(ins_id, opcode, "STRB", False, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm2 = get_bits(opcode, 5, 4)
            Rm = get_bits(opcode, 3, 0)
        
            # if Rn == '1111' then UNDEFINED;
            if Rn == 0b1111:
                raise UnpredictableInstructionException()
            
            index = True
            add = True
            wback = False
            
            shift_t = SRType_LSL
            shift_n = imm2
            
            # if t IN {13,15} || m IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt) or BadReg(Rm):
                raise UnpredictableInstructionException()

            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n))]
            ins = Instruction(ins_id, opcode, "STRB", False, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingA1:
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm5 = get_bits(opcode, 11, 7)
            type_ = get_bits(opcode, 6, 5)
            Rm = get_bits(opcode, 3, 0)
            
            # if P == '0' && W == '1' then SEE STRBT;
            if P == 0 and W == 1:
                # NOTE: Changed encoding
                encoding = eEncodingA2
                return self.decode_strbt(opcode, encoding)
            
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            shift_t, shift_n = DecodeImmShift(type_, imm5)
            
            # if t == 15 || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if wback && (n == 15 || n == t) then UNPREDICTABLE;
            if wback and (Rn == 15 or Rn == Rt):
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and wback and Rm == Rn:
                raise UnpredictableInstructionException()
        
            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, not add), RegisterShift(shift_t, shift_n), wback=False)]
                ins = Instruction(ins_id, opcode, "STRB", False, condition, operands, encoding)
            
            elif index == True and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, not add), RegisterShift(shift_t, shift_n), wback=True)]
                ins = Instruction(ins_id, opcode, "STRB", False, condition, operands, encoding)
            
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, not add), RegisterShift(shift_t, shift_n)]
                ins = Instruction(ins_id, opcode, "STRB", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins
    
    def decode_strb_immediate_thumb(self, opcode, encoding):
        """
        A8.8.206
        STRB (immediate, Thumb)
        Store Register Byte (immediate) calculates an address from a base register value and an immediate offset, and stores
        a byte from a register to memory. It can use offset, post-indexed, or pre-indexed addressing.
        """
        props = {}
        ins_id = ARMInstruction.strb_immediate
        if encoding == eEncodingT1:
            imm32 = get_bits(opcode, 10, 6)
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            index = True
            add = True
            wback = False
            
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "STRB", False, None, operands, encoding)
    
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            
            # if Rn == '1111' then UNDEFINED;
            if Rn == 0b1111:
                raise UndefinedOpcode()
            
            index = True
            add = True
            wback = False
            
            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()

            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "STRB", False, None, operands, encoding, ".W")
        
        elif encoding == eEncodingT3:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            P = get_bit(opcode, 10)
            U = get_bit(opcode, 9)
            W = get_bit(opcode, 8)
            imm32 = get_bits(opcode, 7, 0)
            
            # if P == '1' && U == '1' && W == '0' then SEE STRBT;
            if P == 1 and U == 1 and W == 0:
                return self.decode_strbt(opcode, encoding)
            
            # if Rn == '1111' || (P == '0' && W == '0') then UNDEFINED;
            if Rn == 0b1111 or (P == 0 and W == 0):
                raise UndefinedOpcode()
            
            index = P == 1
            add = U == 1
            wback = W == 1
            
            # if t IN {13,15} || (wback && n == t) then UNPREDICTABLE;
            if BadReg(Rt) or (wback and Rn == Rt):
                raise UnpredictableInstructionException()
            
            if not add:
                imm32 *= -1
                
            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=False)]
                ins = Instruction(ins_id, opcode, "STRB", False, None, operands, encoding)
            
            elif index == True and wback == True:                
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=True)]
                ins = Instruction(ins_id, opcode, "STRB", False, None, operands, encoding)
                
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
                ins = Instruction(ins_id, opcode, "STRB", False, None, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
    
    def decode_strb_immediate_arm(self, opcode, encoding):
        """
        A8.8.207
        STRB (immediate, ARM)
        Store Register Byte (immediate) calculates an address from a base register value and an immediate offset, and stores
        a byte from a register to memory. It can use offset, post-indexed, or pre-indexed addressing.
        
        Syntax:
        STRB{<c>}{<q>} <Rt>, [<Rn> {, #+/-<imm>}]  Offset: index==TRUE, wback==FALSE
        STRB{<c>}{<q>} <Rt>, [<Rn>, #+/-<imm>]!    Pre-indexed: index==TRUE, wback==TRUE
        STRB{<c>}{<q>} <Rt>, [<Rn>], #+/-<imm>     Post-indexed: index==FALSE, wback==TRUE            
        """
        props = {}
        ins_id = ARMInstruction.strb_immediate
        condition = self.decode_condition_field(opcode)
        
        P = get_bit(opcode, 24)
        U = get_bit(opcode, 23)
        W = get_bit(opcode, 21)
        Rn = get_bits(opcode, 19, 16)
        Rt = get_bits(opcode, 15, 12)
        imm12 = get_bits(opcode, 11, 0)
        
        # if P == '0' && W == '1' then SEE STRBT;
        if P == 0 and W == 1:
            return self.decode_strbt(opcode, encoding)
        
        # if t == 15 then UNPREDICTABLE;
        if Rt == 15:
            raise UnpredictableInstructionException()
        
        index = P == 1
        add = U == 1
        wback = P == 0 or W == 1
        
        if not add:
            imm12 *= -1
        
        # if wback && (n == 15 || n == t) then UNPREDICTABLE;
        if wback == True and Rn == Rt:
            raise UnpredictableInstructionException()
        
        if index == True and wback == False:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm12), wback=False)]
            ins = Instruction(ins_id, opcode, "STRB", False, condition, operands, encoding)
        
        elif index == True and wback == True:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm12), wback=True)]
            ins = Instruction(ins_id, opcode, "STRB", False, condition, operands, encoding)
        
        elif index == False and wback == True:
            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm12)]
            ins = Instruction(ins_id, opcode, "STRB", False, condition, operands, encoding)

        return ins
    
    def decode_strbt(self, opcode, encoding):
        """
        A8.8.209
        STRBT
        Store Register Byte Unprivileged stores a byte from a register to memory.
        
        Syntax:
        STRBT{<c>}{<q>} <Rt>, [<Rn> {, #<imm>}]             Offset: Thumb only
        STRBT{<c>}{<q>} <Rt>, [<Rn>] {, #<imm>}             Post-indexed: ARM only
        STRBT{<c>}{<q>} <Rt>, [<Rn>], +/-<Rm> {, <shift>}   Post-indexed: ARM only
        """
        props = {}
        ins_id = ARMInstruction.strbt
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 7, 0)
            
            # if Rn == '1111' then UNDEFINED;
            if Rn == 0b1111:
                raise UnpredictableInstructionException()
            
            postindex = False
            add = True
            register_form = False
            
            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "STRBT", False, condition, operands, encoding)
            
        elif encoding == eEncodingA1:
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            add = U == 1
            register_form = False
            
            # if t == 15 || n == 15 || n == t then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt:
                raise UnpredictableInstructionException()
            
            if not add:
                imm32 *= -1

            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "STRBT", False, condition, operands, encoding)
        
        elif encoding == eEncodingA2:
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm5 = get_bits(opcode, 11, 7)
            type_ = get_bits(opcode, 6, 5)
            Rm = get_bits(opcode, 3, 0)
            
            post_index = True
            add = U == 1
            register_form = True
            
            shift_t, shift_n = DecodeImmShift(type_, imm5)
            
            # if t == 15 || n == 15 || n == t || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and Rm == Rn:
                raise UnpredictableInstructionException()
            
            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, not add), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "STRBT", False, condition, operands, encoding)
        
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins
    
    def decode_ldrb_immediate_thumb(self, opcode, encoding):
        """
        A8.8.67
        LDRB (immediate, Thumb)
        Load Register Byte (immediate) calculates an address from a base register value and an immediate offset, loads a
        byte from memory, zero-extends it to form a 32-bit word, and writes it to a register. It can use offset, post-indexed,
        or pre-indexed addressing. 
        """
        props = {}
        ins_id = ARMInstruction.ldrb_immediate
        if encoding == eEncodingT1:
            imm32 = get_bits(opcode, 10, 6)
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            index = True
            add = True
            wback = False
            
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDRB", False, None, operands, encoding)
        
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16) 
            imm32 = get_bits(opcode, 11, 0)
            Rt = get_bits(opcode, 15, 12)
            index = True
            add = True
            wback = False
            
            # if Rt == '1111' then SEE PLD;
            if Rt == 0b1111:
                return self.decode_pld(opcode, encoding)
            
            # if Rn == '1111' then SEE LDRB (literal);
            if Rn == 0b1111:
                return self.decode_ldrb_literal(opcode, encoding)
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                return UnpredictableInstructionException()
            
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDRB", False, None, operands, encoding, ".W")
        
        elif encoding == eEncodingT3:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 7, 0)
            P = get_bit(opcode, 10)
            U = get_bit(opcode, 9)
            W = get_bit(opcode, 8)
            
            # if Rt == '1111' && P == '1' && U == '0' && W == '0' then SEE PLD, PLDW (immediate);
            if Rt == 0b1111 and P == 1 and U == 0 and W == 0:
                raise InstructionNotImplementedException("SEE PLD, PLDW (immediate);")
            
            # if Rn == '1111' then SEE LDRB (literal);
            if Rn == 0b1111:
                return self.decode_ldrb_literal(opcode, encoding)
            
            # if P == '1' && U == '1' && W == '0' then SEE LDRBT;
            if P == 1 and U == 1 and W == 0:
                return self.decode_ldrbt(opcode, encoding)
            
            # if P == '0' && W == '0' then UNDEFINED;
            if P == 0 and W == 0:
                raise UndefinedOpcode()

            index = P == 1
            add = U == 1
            wback = W == 1
            
            # if t == 13 || (t == 15 && W == '1') || (wback && n == t) then UNPREDICTABLE;
            if Rt == 13 or (Rt == 15 and W == 1) or (wback and Rt == Rn):
                raise UnpredictableInstructionException()

            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=False)]
                ins = Instruction(ins_id, opcode, "LDRB", False, None, operands, encoding)
            
            elif index == True and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=True)]
                ins = Instruction(ins_id, opcode, "LDRB", False, None, operands, encoding)
            
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
                ins = Instruction(ins_id, opcode, "LDRB", False, None, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
    
    def decode_ldrb_immediate_arm(self, opcode, encoding):
        """
        A8.8.68
        LDRB (immediate, ARM)
        Load Register Byte (immediate) calculates an address from a base register value and an immediate offset, loads a
        byte from memory, zero-extends it to form a 32-bit word, and writes it to a register. It can use offset, post-indexed,
        or pre-indexed addressing.
        
        Syntax:
        LDRB{<c>}{<q>} <Rt>, [<Rn> {, #+/-<imm>}]  Offset: index==TRUE, wback==FALSE
        LDRB{<c>}{<q>} <Rt>, [<Rn>, #+/-<imm>]!    Pre-indexed: index==TRUE, wback==TRUE
        LDRB{<c>}{<q>} <Rt>, [<Rn>], #+/-<imm>     Post-indexed: index==FALSE, wback==TRUE
        """
        props = {}
        ins_id = ARMInstruction.ldrb_immediate
        condition = self.decode_condition_field(opcode)
        
        P = get_bit(opcode, 24)
        U = get_bit(opcode, 23)
        W = get_bit(opcode, 21)
        Rn = get_bits(opcode, 19, 16)
        Rt = get_bits(opcode, 15, 12)
        imm12 = get_bits(opcode, 11, 0)
        
        # if Rn == '1111' then SEE LDRB (literal);
        if Rn == 0b1111:
            return self.decode_ldrb_literal(opcode, encoding)
        
        # if P == '0' && W == '1' then SEE LDRBT;
        if P == 0 and W == 1:
            return self.decode_ldrbt(opcode, encoding)
                
        index = P == 1
        add = U == 1
        wback = P == 0 or W == 1
        
        if not add:
            imm12 *= -1
        
        # if t == 15 || (wback && n == t) then UNPREDICTABLE;
        if Rt == 15 or (wback == True and Rn == Rt):
            raise UnpredictableInstructionException()
        
        if index == True and wback == False:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm12), wback=True)]
            ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding)
        
        elif index == True and wback == True:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm12), wback=True)]
            ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding)
        
        elif index == False and wback == True:
            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm12)]
            ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding)

        return ins
    
    def decode_ldrb_literal(self, opcode, encoding):
        """
        A8.8.69
        LDRB (literal)
        Load Register Byte (literal) calculates an address from the PC value and an immediate offset, loads a byte from
        memory, zero-extends it to form a 32-bit word, and writes it to a register        
        
        Syntax:
        LDRB{<c>}{<q>} <Rt>, <label>          Normal form
        LDRB{<c>}{<q>} <Rt>, [PC, #+/-<imm>]  Alternative form
        """
        props = {}
        ins_id = ARMInstruction.ldrb_literal
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            U = get_bit(opcode, 23)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            add = U == 1
            
            # if Rt == '1111' then SEE PLD;
            if Rt == 0b111:
                return self.decode_pld(opcode, encoding)
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            U = get_bit(opcode, 23)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            add = U == 1
            
            # if t == 15 then UNPREDICTABLE;
            if Rt == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                        
        if not add:
            imm32 *= -1
            
        operands = [Register(Rt), Memory(ARMRegister.PC, Immediate(imm32))]
        ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding)            
        return ins
    
    def decode_ldrb_register(self, opcode, encoding):
        """
        A8.8.70
        LDRB (register)
        Load Register Byte (register) calculates an address from a base register value and an offset register value, loads a
        byte from memory, zero-extends it to form a 32-bit word, and writes it to a register. The offset register value can
        optionally be shifted.         
        
        Syntax:
        LDRB{<c>}{<q>} <Rt>, [<Rn>, +/-<Rm>{, <shift>}]   Offset: index==TRUE, wback==FALSE
        LDRB{<c>}{<q>} <Rt>, [<Rn>, +/-<Rm>{, <shift>}]!  Pre-indexed: index==TRUE, wback==TRUE
        LDRB{<c>}{<q>} <Rt>, [<Rn>], +/-<Rm>{, <shift>}   Post-indexed: index==FALSE, wback==TRUE
        """
        props = {}
        ins_id = ARMInstruction.ldrb_register
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rm = get_bits(opcode, 8, 6)
            Rn = get_bits(opcode, 5, 3)
            Rt = get_bits(opcode, 2, 0)
            
            index = True
            add = True
            wback = False
            
            shift_t = SRType_LSL
            shift_n = 0

            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm))]
            ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding)
                                    
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm2 = get_bits(opcode, 5, 4)
            Rm = get_bits(opcode, 3, 0)
        
            # if Rt == '1111' then SEE PLD;
            if Rt == 0b1111:
                return self.decode_pld(opcode, encoding)

            # if Rn == '1111' then SEE LDRB (literal);
            if Rn == 0b1111:
                return self.decode_ldrb_literal(opcode, encoding)
            
            index = True
            add = True
            wback = False
            
            shift_t = SRType_LSL
            shift_n = imm2
            
            # if t == 13 || m IN {13,15} then UNPREDICTABLE;
            if Rt == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n))]
            ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding, ".W")
                        
        elif encoding == eEncodingA1:
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm5 = get_bits(opcode, 11, 7)
            type_ = get_bits(opcode, 6, 5)
            Rm = get_bits(opcode, 3, 0)
            
            # if P == '0' && W == '1' then SEE LDRBT;
            if P == 0 and W == 1:
                # NOTE: Encoding changed.
                encoding = eEncodingA2
                return self.decode_ldrbt(opcode, encoding)
            
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            shift_t, shift_n = DecodeImmShift(type_, imm5)
            
            # if t == 15 || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if wback && (n == 15 || n == t) then UNPREDICTABLE;
            if wback and (Rn == 15 or Rn == Rt):
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and wback and Rm == Rn:
                raise UnpredictableInstructionException()
                        
            if index == True and wback == False:
                operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, not add), RegisterShift(shift_t, shift_n), wback=False)]
                ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding)
            
            elif index == True and wback == True:
                operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, not add), RegisterShift(shift_t, shift_n), wback=True)]
                ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding)
            
            elif index == False and wback == True:
                operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, not add), RegisterShift(shift_t, shift_n)]
                ins = Instruction(ins_id, opcode, "LDRB", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        return ins
    
    def decode_ldrbt(self, opcode, encoding):
        """
        A8.8.71
        LDRBT
        Load Register Byte Unprivileged loads a byte from memory, zero-extends it to form a 32-bit word, and writes it to
        a register.
        
        Syntax:
        LDRBT{<c>}{<q>} <Rt>, [<Rn> {, #<imm>}]
        LDRBT{<c>}{<q>} <Rt>, [<Rn>] {, #+/-<imm>}
        LDRBT{<c>}{<q>} <Rt>, [<Rn>], +/-<Rm> {, <shift>}
        """
        props = {}
        ins_id = ARMInstruction.ldrbt
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 7, 0)
            
            # if Rn == '1111' then SEE LDRB (literal);
            if Rn == 0b1111:
                return self.decode_ldrb_literal(opcode, encoding)
            
            postindex = False
            add = True
            register_form = False
            
            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
            ins = Instruction(ins_id, opcode, "LDRBT", False, condition, operands, encoding)
            
        elif encoding == eEncodingA1:
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm32 = get_bits(opcode, 11, 0)
            add = U == 1
            register_form = False
            
            # if t == 15 || n == 15 || n == t then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt:
                raise UnpredictableInstructionException()
            
            if not add:
                imm32 *= -1

            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
            ins = Instruction(ins_id, opcode, "LDRBT", False, condition, operands, encoding)
        
        elif encoding == eEncodingA2:
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            Rt = get_bits(opcode, 15, 12)
            imm5 = get_bits(opcode, 11, 7)
            type_ = get_bits(opcode, 6, 5)
            Rm = get_bits(opcode, 3, 0)
            
            post_index = True
            add = U == 1
            register_form = True
            
            shift_t, shift_n = DecodeImmShift(type_, imm5)
            
            # if t == 15 || n == 15 || n == t || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and Rm == Rn:
                raise UnpredictableInstructionException()

            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, add == False), RegisterShift(shift_t, shift_n)]
            ins = Instruction(ins_id, opcode, "LDRBT", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins

    def decode_stmda(self, opcode, encoding):
        """
        A8.8.200
        STMDA (STMED)
        Store Multiple Decrement After (Store Multiple Empty Descending) stores multiple registers to consecutive
        memory locations using an address from a base register. The consecutive memory locations end at this address, and
        the address just below the lowest of those locations can optionally be written back to the base register.     
        
        Syntax:   
        STMDA{<c>}{<q>} <Rn>{!}, <registers>
        """
        props = {}
        ins_id = ARMInstruction.stmda
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            registers = get_bits(opcode, 15, 0)
            wback = get_bit(opcode, 21)
              
            # if n == 15 || BitCount(registers) < 1 then UNPREDICTABLE;
            if (Rn == 15) or (BitCount (registers) < 1):
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        operands = [Register(Rn, wback), RegisterSet(registers)]
        ins = Instruction(ins_id, opcode, "STMDA", False, condition, operands, encoding)
        return ins
        
    def decode_ldmda(self, opcode, encoding):
        """
        A8.8.59
        LDMDA/LDMFA
        Load Multiple Decrement After (Load Multiple Full Ascending) loads multiple registers from consecutive memory
        locations using an address from a base register. The consecutive memory locations end at this address, and the
        address just below the lowest of those locations can optionally be written back to the base register. The registers
        loaded can include the PC, causing a branch to a loaded address.
        
        Syntax:
        LDMDA{<c>}{<q>} <Rn>{!}, <registers>
        
        Unit-test: OK
        """
        props = {}
        ins_id = ARMInstruction.ldmda
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            registers = get_bits(opcode, 15, 0)
            wback = get_bit(opcode, 21)
              
            # if n == 15 || BitCount(registers) < 1 then UNPREDICTABLE;
            if (Rn == 15) or (BitCount (registers) < 1):
                raise UnpredictableInstructionException()
            
            # if wback && registers<n> == '1' && ArchVersion() >= 7 then UNPREDICTABLE;
            if wback and get_bit(registers, Rn) and self.ArchVersion() > 7:
                raise UnpredictableInstructionException()             

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        operands = [Register(Rn, wback), RegisterSet(registers)]
        ins = Instruction(ins_id, opcode, "LDMDA", False, condition, operands, encoding)            
        return ins
        
    def decode_stmia(self, opcode, encoding):
        """
        A8.8.199
        STM (STMIA, STMEA)
        Store Multiple Increment After (Store Multiple Empty Ascending) stores multiple registers to consecutive memory
        locations using an address from a base register. The consecutive memory locations start at this address, and the
        address just above the last of those locations can optionally be written back to the base register.
        
        Syntax:
        STM{<c>}{<q>} <Rn>{!}, <registers>        
        """
        props = {}
        ins_id = ARMInstruction.stmia
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            # TODO
            # if CurrentInstrSet() == InstrSet_ThumbEE then SEE "ThumbEE instructions";
            Rn = get_bits(opcode, 10, 8)
            registers = 0b0000000000000000 | get_bits(opcode, 7, 0)
            wback = 1

            # if BitCount(registers) < 1 then UNPREDICTABLE;
            if BitCount (registers) < 1:
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Register(Rn, wback), RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "STM", False, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            Rn = get_bits(opcode, 19, 16)
            M = get_bit(opcode, 14)
            wback = get_bit(opcode, 21)
            registers = ((0b000 | (M << 1)) << 13) | get_bits(opcode, 12, 0)
              
            # if n == 15 || BitCount(registers) < 2 then UNPREDICTABLE;
            if (Rn == 15) or (BitCount (registers) < 2):
                raise UnpredictableInstructionException()
            
            # if wback && registers<n> == '1' then UNPREDICTABLE;
            if wback and get_bit(registers, Rn):
                raise UnpredictableInstructionException()             

            condition = None
            operands = [Register(Rn, wback), RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "STM", False, condition, operands, encoding, ".W")

        elif encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            wback = get_bit(opcode, 21)
            registers = get_bits(opcode, 15, 0)
              
            # if n == 15 || BitCount(registers) < 1 then UNPREDICTABLE;
            if (Rn == 15) or (BitCount (registers) < 1):
                raise UnpredictableInstructionException()

            operands = [Register(Rn, wback), RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "STM", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
            
    def decode_ldmia_arm(self, opcode, encoding):
        """
        A8.8.58
        LDM/LDMIA/LDMFD (ARM)
        Load Multiple Increment After (Load Multiple Full Descending) loads multiple registers from consecutive memory
        locations using an address from a base register. The consecutive memory locations start at this address, and the
        address just above the highest of those locations can optionally be written back to the base register. The registers
        loaded can include the PC, causing a branch to a loaded address.

        Syntax:
        LDM{<c>}{<q>} <Rn>{!}, <registers>
                
        Unit-test: OK       
        """
        props = {}
        ins_id = ARMInstruction.ldmia
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            registers = get_bits(opcode, 15, 0)
            W = wback = get_bit(opcode, 21)
              
            # if W == '1' && Rn == '1101' && BitCount(register_list) > 1 then SEE POP (ARM);
            if W == 1 and Rn == 0b1101 and BitCount(registers) > 1:
                return self.decode_pop_arm(opcode, encoding)
              
            # if n == 15 || BitCount(registers) < 1 then UNPREDICTABLE;
            if (Rn == 15) or (BitCount (registers) < 1):
                raise UnpredictableInstructionException()
            
            # if wback && registers<n> == '1' && ArchVersion() >= 7 then UNPREDICTABLE;
            if wback and get_bit(registers, Rn) and self.ArchVersion() >= 7:
                raise UnpredictableInstructionException()             

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        # This is just for the unit test so objdump's format and ours match.
        if Rn == 13 and BitCount(registers) == 1:
            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "POP", False, condition, operands, encoding)            
            
        else:
            operands = [Register(Rn, wback), RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "LDM", False, condition, operands, encoding)            

        return ins
        
    def decode_pld(self, opcode, encoding):
        """
        A8.8.126
        PLD, PLDW (immediate)
        Preload Data signals the memory system that data memory accesses from a specified address are likely in the near
        future. The memory system can respond by taking actions that are expected to speed up the memory accesses when
        they do occur, such as pre-loading the cache line containing the specified address into the data cache
        """
        props = {}
        ins_id = ARMInstruction.pld
        if encoding == eEncodingT1:
            # PLD{W}<c> [<Rn>, #<imm12>]
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            imm32 = get_bits(opcode, 11, 0)
            
            # if Rn == '1111' then SEE PLD (literal);
            if Rn == 0b1111:
                return self.decode_pld_literal(opcode, encoding)
            
            # n = UInt(Rn); imm32 = ZeroExtend(imm12, 32); add = TRUE; is_pldw = (W == '1');
            is_pldw = W == 1
            add = True
        
        elif encoding == eEncodingT2:
            # PLD{W}<c> [<Rn>, #-<imm8>]
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            imm32 = get_bits(opcode, 7, 0)

            # if Rn == '1111' then SEE PLD (literal);
            if Rn == 0b1111:
                return self.decode_pld_literal(opcode, encoding)
            
            # n = UInt(Rn); imm32 = ZeroExtend(imm8, 32); add = FALSE; is_pldw = (W == '1');
            is_pldw = W == 1
            add = False
            imm32 *= -1
    
        elif encoding == eEncodingA1:
            # PLD{W} [<Rn>, #+/-<imm12>]
            R = get_bit(opcode, 22)
            U = get_bit(opcode, 23)
            Rn = get_bits(opcode, 19, 16)
            imm32 = get_bits(opcode, 11, 0)
            
            # if Rn == '1111' then SEE PLD (literal);
            if Rn == 0b1111:
                return self.decode_pld_literal(opcode, encoding)
            
            # n = UInt(Rn); imm32 = ZeroExtend(imm12, 32); add = (U == '1'); is_pldw = (R == '0');
            add = U == 1
            is_pldw = R == 0
            
            if not add:
                imm32 *= -1

        qual = "W" if is_pldw else ""

        operands = [Memory(Register(Rn), Immediate(imm32))]
        ins = Instruction(ins_id, opcode, "PLD", False, None, operands, encoding, qual)
        return ins
    
    def decode_pop_thumb(self, opcode, encoding):
        """
        A8.8.131
        POP (Thumb)
        Pop Multiple Registers loads multiple registers from the stack, loading from consecutive memory locations starting
        at the address in SP, and updates SP to point just above the loaded data.        
        """
        props = {}
        ins_id = ARMInstruction.pop
        if encoding == eEncodingT1:
            P = get_bit(opcode, 8)
            register_list = get_bits(opcode, 7, 0)
            UnalignedAllowed = False
            
            # registers = P:'0000000':register_list;
            registers = (P << (8 + 7)) | register_list

            # if BitCount(registers) < 1 then UNPREDICTABLE;
            if BitCount(registers) < 1:
                raise UnpredictableInstructionException()
            
            # if registers<15> == '1' && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if get_bit(registers, 15) == 1 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
            
            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "POP", False, None, operands, encoding)
        
        elif encoding == eEncodingT2:
            P = get_bit(opcode, 15)
            M = get_bit(opcode, 14)
            register_list = get_bits(opcode, 12, 0)
            UnalignedAllowed = False
            
            # registers = P:M:'0':register_list; UnalignedAllowed = FALSE;
            registers = (P << (2 + 13)) | (M << (13 + 1)) | register_list
            
            # if BitCount(registers) < 2 || (P == '1' && M == '1') then UNPREDICTABLE;
            if BitCount(registers) < 2 or (P == 1 and M == 1):
                raise UnpredictableInstructionException()
            
            # if registers<15> == '1' && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if get_bit(registers, 15) == 1 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "POP", False, None, operands, encoding, ".W")

        elif encoding == eEncodingT3:
            Rt = get_bits(opcode, 15, 12)
            registers = 1 << Rt
            UnalignedAllowed = True
            
            # if t == 13 || (t == 15 && InITBlock() && !LastInITBlock()) then UNPREDICTABLE;
            if Rt == 13 or (Rt == 15 and self.InITBlock() and not self.LastInITBlock()):
                raise UnpredictableInstructionException()
            
            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "POP", False, None, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
    
    def decode_pop_arm(self, opcode, encoding):
        """
        A8.8.132
        POP (ARM)
        Pop Multiple Registers loads multiple registers from the stack, loading from consecutive memory locations starting
        at the address in SP, and updates SP to point just above the loaded data.
        
        Syntax:
        POP{<c>}{<q>} <registers>       Standard syntax
        LDM{<c>}{<q>} SP!, <registers>  Equivalent LDM syntax
        """
        props = {}
        ins_id = ARMInstruction.pop
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            registers = get_bits(opcode, 15, 0)
              
            # if BitCount(register_list) < 2 then SEE LDM / LDMIA / LDMFD;
            if BitCount (registers) < 2:
                return self.decode_ldmia_arm(opcode, encoding)
            
            # if registers<13> == '1' && ArchVersion() >= 7 then UNPREDICTABLE;
            if get_bit(registers, 13) and self.ArchVersion() >= 7:
                raise UnpredictableInstructionException()
            
        elif encoding == eEncodingA2:
            Rt = get_bits(opcode, 15, 12)
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()
            
            registers = 1 << Rt

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        operands = [RegisterSet(registers)]
        ins = Instruction(ins_id, opcode, "POP", False, condition, operands, encoding)
        return ins
        
    def decode_stmdb(self, opcode, encoding):
        """
        A8.8.201
        STMDB (STMFD)
        Store Multiple Decrement Before (Store Multiple Full Descending) stores multiple registers to consecutive memory
        locations using an address from a base register. The consecutive memory locations end just below this address, and
        the address of the first of those locations can optionally be written back to the base register.        
        
        Syntax:
        STMDB{<c>}{<q>} <Rn>{!}, <registers>
        """
        props = {}
        ins_id = ARMInstruction.stmdb
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 19, 16)
            wback = get_bit(opcode, 21)
            M = get_bit(opcode, 14)
            registers = ((0b000 | (M << 1)) << 13) | get_bits(opcode, 12, 0)
            
            # if W == '1' && Rn == '1101' then SEE PUSH;
            if wback and Rn == 13:
                return self.decode_push(opcode, encoding)

            # if n == 15 || BitCount(registers) < 2 then UNPREDICTABLE;
            if (Rn == 15) or (BitCount (registers) < 2):
                raise UnpredictableInstructionException()
            
            # if wback && registers<n> == '1' then UNPREDICTABLE;
            if wback and get_bit(registers, Rn):
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            wback = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            registers = get_bits(opcode, 15, 0)

            # if W == '1' && Rn == '1101' && BitCount(register_list) >= 2 then SEE PUSH;
            if wback and Rn == 13 and BitCount(registers) >= 2:
                return self.decode_push(opcode, encoding)

            # if n == 15 || BitCount(registers) < 1 then UNPREDICTABLE;
            if (Rn == 15) or (BitCount (registers) < 1):
                raise UnpredictableInstructionException()            

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        if wback:
            wback = "!"
        
        # Check if SP. This is for the unit test to compare with objdump correctly
        if Rn == 13:
            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "PUSH", False, condition, operands, encoding)
            
        else:
            operands = [Register(Rn, wback), RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "STMDB", False, condition, operands, encoding)
            
        return ins        
        
    def decode_push(self, opcode, encoding):
        """
        A8.8.133
        PUSH
        Push Multiple Registers stores multiple registers to the stack, storing to consecutive memory locations ending just
        below the address in SP, and updates SP to point to the start of the stored data.
        
        Syntax:
        PUSH{<c>}{<q>} <registers>        Standard syntax
        STMDB{<c>}{<q>} SP!, <registers>  Equivalent STM syntax
        """
        props = {}
        ins_id = ARMInstruction.push
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            M = get_bit(opcode, 8)
            registers = get_bits(opcode, 7, 0)
            registers = (M << (8 + 6)) | get_bits(opcode, 7, 0)

            # if BitCount(registers) < 1 then UNPREDICTABLE;
            if BitCount (registers) < 1:
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "PUSH", False, condition, operands, encoding)
            
        elif encoding == eEncodingT2:
            M = get_bit(opcode, 14)
            registers = (M << (13 + 1)) | get_bits(opcode, 12, 0)
              
            # if BitCount(registers) < 2 then UNPREDICTABLE;
            if BitCount (registers) < 2:
                raise UnpredictableInstructionException()

            condition = None
            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "PUSH", False, condition, operands, encoding, ".W")

        elif encoding == eEncodingT3:
            Rt = get_bits(opcode, 15, 12)
            registers = 1 << Rt
              
            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()

            condition = None
            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "PUSH", False, condition, operands, encoding, ".W")            
                         
        elif encoding == eEncodingA1:
            registers = get_bits(opcode, 15, 0)
            
            # if BitCount(register_list) < 2 then SEE STMDB / STMFD;
            if BitCount(registers) < 2:
                return self.decode_stmdb(opcode, encoding)

            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "PUSH", False, condition, operands, encoding)
            
        elif encoding == eEncodingA2:
            Rt = get_bits(opcode, 15, 12)
            registers = 1 << Rt
              
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()             

            operands = [RegisterSet(registers)]
            ins = Instruction(ins_id, opcode, "PUSH", False, condition, operands, encoding)            

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                    
        return ins
    
    def decode_ldmia_thumb(self, opcode, encoding):
        """
        A8.8.57
        LDM/LDMIA/LDMFD (Thumb)
        Load Multiple Increment After (Load Multiple Full Descending) loads multiple registers from consecutive memory
        locations using an address from a base register. The consecutive memory locations start at this address, and the
        address just above the highest of those locations can optionally be written back to the base register. The registers
        loaded can include the PC, causing a branch to a loaded address. 
        """
        props = {}
        ins_id = ARMInstruction.ldmia
        if encoding == eEncodingT1:
            Rn = get_bits(opcode, 10, 8)
            register_list = get_bits(opcode, 7, 0)
            
            # TODO:
            # if CurrentInstrSet() == InstrSet_ThumbEE then SEE "ThumbEE instructions";
            wback = get_bit(register_list, Rn) == 0
            
            # if BitCount(registers) < 1 then UNPREDICTABLE;
            if BitCount(register_list) < 1:
                raise UnpredictableInstructionException()
        
            operands = [Register(Rn, wback), RegisterSet(register_list)]
            ins = Instruction(ins_id, opcode, "LDMIA", False, None, operands, encoding)
        
        elif encoding == eEncodingT2:
            W = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            P = get_bit(opcode, 15)
            M = get_bit(opcode, 14)
            register_list = get_bits(opcode, 12, 0)
            
            # if W == '1' && Rn == '1101' then SEE POP (Thumb);
            if W == 1 and Rn == 0b1101:
                return self.decode_pop_thumb(opcode, encoding)
        
            # registers = P:M:'0':register_list;
            registers = (P << 15) | (M << 14) | register_list
            wback = W == 1
            
            # if n == 15 || BitCount(registers) < 2 || (P == '1' && M == '1') then UNPREDICTABLE;
            if Rn == 15 or BitCount(registers) < 2 or (P == 1 and M == 1):
                raise UnpredictableInstructionException()
            
            # if registers<15> == '1' && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if get_bit(registers, 15) == 1 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
            
            # if wback && registers<n> == '1' then UNPREDICTABLE;
            if wback and get_bit(registers, Rn) == 1:
                raise UnpredictableInstructionException()

            operands = [Register(Rn, wback), RegisterSet(register_list)]
            ins = Instruction(ins_id, opcode, "LDMIA", False, None, operands, encoding, ".W")

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
    
    def decode_ldmdb(self, opcode, encoding):
        """
        A8.8.60
        LDMDB/LDMEA
        Load Multiple Decrement Before (Load Multiple Empty Ascending) loads multiple registers from consecutive
        memory locations using an address from a base register. The consecutive memory locations end just below this
        address, and the address of the lowest of those locations can optionally be written back to the base register. The
        registers loaded can include the PC, causing a branch to a loaded address.
        
        Syntax:
        LDMDB{<c>}{<q>} <Rn>{!}, <registers>
        
        Unit-test: OK
        """
        props = {}
        ins_id = ARMInstruction.ldmdb
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            wback = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            P = get_bit(opcode, 15)
            M = get_bit(opcode, 14)
            registers = get_bits(opcode, 12, 0)
            
            # if n == 15 || BitCount(registers) < 2 || (P == '1' && M == '1') then UNPREDICTABLE;
            if Rn == 15 or BitCount(registers) < 2 or (P == 1 and M == 1):
                raise UnpredictableInstructionException()
            
            # if registers<15> == '1' && InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if get_bit(registers, 15) == 1 and self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
            
            # if wback && registers<n> == '1' then UNPREDICTABLE; 
            if wback and get_bit(registers, Rn) == 1:
                raise UnpredictableInstructionException()
            
            condition = None
            
        elif encoding == eEncodingA1:
            wback = get_bit(opcode, 21)
            Rn = get_bits(opcode, 19, 16)
            registers = get_bits(opcode, 15, 0)
            
            # if n == 15 || BitCount(registers) < 1 then UNPREDICTABLE;
            if Rn == 15 or BitCount(registers) < 1:
                raise UnpredictableInstructionException()
            
            # if wback && registers<n> == '1' && ArchVersion() >= 7 then UNPREDICTABLE;
            if wback and get_bit(registers, Rn) == 1and self.ArchVersion() >= 7:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rn, wback), RegisterSet(registers)]
        ins = Instruction(ins_id, opcode, "LDMDB", False, condition, operands, encoding)            
        return ins
        
    def decode_stmib(self, opcode, encoding):
        """
        A8.8.202
        STMIB (STMFA)
        Store Multiple Increment Before (Store Multiple Full Ascending) stores multiple registers to consecutive memory
        locations using an address from a base register. The consecutive memory locations start just above this address, and
        the address of the last of those locations can optionally be written back to the base register.        
        
        Syntax:
        STMIB{<c>}{<q>} <Rn>{!}, <registers>
        """
        props = {}
        ins_id = ARMInstruction.stmib
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            wback = get_bit(opcode, 21)
            registers = get_bits(opcode, 15, 0)
            
            # if n == 15 || BitCount(registers) < 1 then UNPREDICTABLE;
            if Rn == 15 or BitCount(registers) < 1:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rn, wback), RegisterSet(registers)]
        ins = Instruction(ins_id, opcode, "STMIB", False, condition, operands, encoding)
        return ins
        
    def decode_ldmib(self, opcode, encoding):
        """
        A8.8.61
        LDMIB/LDMED
        Load Multiple Increment Before (Load Multiple Empty Descending) loads multiple registers from consecutive
        memory locations using an address from a base register. The consecutive memory locations start just above this
        address, and the address of the last of those locations can optionally be written back to the base register. The registers
        loaded can include the PC, causing a branch to a loaded address.

        Syntax:
        LDMIB{<c>}{<q>} <Rn>{!}, <registers>

        Unit-test: OK               
        """
        props = {}
        ins_id = ARMInstruction.ldmib
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            wback = get_bit(opcode, 21)
            registers = get_bits(opcode, 15, 0)
            
            # if n == 15 || BitCount(registers) < 1 then UNPREDICTABLE;
            if Rn == 15 or BitCount(registers) < 1:
                raise UnpredictableInstructionException()
            
            # if wback && registers<n> == '1' && ArchVersion() >= 7 then UNPREDICTABLE;
            if wback and get_bit(registers, Rn) and self.ArchVersion() >= 7:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rn, wback), RegisterSet(registers)]
        ins = Instruction(ins_id, opcode, "LDMIB", False, condition, operands, encoding)            
        return ins
        
    def decode_stm_user_registers(self, opcode, encoding):
        """
        STM (User registers)
        In a PL1 mode other than System mode, Store Multiple (user registers) stores multiple User mode registers to
        consecutive memory locations using an address from a base register. The processor reads the base register value
        normally, using the current mode to determine the correct Banked version of the register. This instruction cannot
        writeback to the base register.
        STM (User registers) is UNDEFINED in Hyp mode, and UNPREDICTABLE in User or System modes.
        
        Syntax:
        """
        props = {}
        ins_id = ARMInstruction.stm_user_registers
        condition = self.decode_condition_field(opcode)
                
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            registers = get_bits(opcode, 15, 0)
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            
            if Rn == 15 or BitCount(registers) < 1:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if P == 0 and U == 0:
            amode = "DA"
        elif P == 1 and U == 0:
            amode = "DB"
        elif P == 0 and U == 1:
            amode = "IA"
        elif P == 1 and U == 1:
            amode = "IB"
                    
        return "STM%s%s %s, %s^" % (condition, amode, Register(Rn), RegisterSet(registers))
    
    def decode_ldm_user_registers(self, opcode, encoding):
        """
        LDM (User registers)
        In a PL1 mode other than System mode, Load Multiple (User registers) loads multiple User mode registers from
        consecutive memory locations using an address from a base register. The registers loaded cannot include the PC.
        The processor reads the base register value normally, using the current mode to determine the correct Banked
        version of the register. This instruction cannot writeback to the base register.
        LDM (user registers) is UNDEFINED in Hyp mode, and UNPREDICTABLE in User and System modes.
        
        Syntax:
        
        Unit-test: OK
        """
        props = {}
        ins_id = ARMInstruction.ldm_user_registers
        condition = self.decode_condition_field(opcode)
                
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            registers = get_bits(opcode, 14, 0)
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            
            if Rn == 15 or BitCount(registers) < 1:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if P == 0 and U == 0:
            amode = "DA"
        elif P == 1 and U == 0:
            amode = "DB"
        elif P == 0 and U == 1:
            amode = "IA"
        elif P == 1 and U == 1:
            amode = "IB"
                    
        return "LDM%s%s %s, %s^" % (condition, amode, Register(Rn), RegisterSet(registers))
        
    def decode_ldm_exception_return(self, opcode, encoding):
        """
        LDM (exception return)
        Load Multiple (exception return) loads multiple registers from consecutive memory locations using an address from
        a base register. The SPSR of the current mode is copied to the CPSR. An address adjusted by the size of the data
        loaded can optionally be written back to the base register.
        The registers loaded include the PC. The word loaded for the PC is treated as an address and a branch occurs to that
        address.        
        
        Syntax:
        
        Unit-test: OK
        """
        props = {}
        ins_id = ARMInstruction.ldm_exception_return
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingA1:
            Rn = get_bits(opcode, 19, 16)
            registers = get_bits(opcode, 14, 0)
            P = get_bit(opcode, 24)
            U = get_bit(opcode, 23)
            wback = get_bit(opcode, 21)
            
            if Rn == 15:
                raise UnpredictableInstructionException()
            
            if wback and get_bit(registers, Rn) and self.ArchVersion() >= 7:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        if P == 0 and U == 0:
            amode = "DA"
        elif P == 1 and U == 0:
            amode = "DB"
        elif P == 0 and U == 1:
            amode = "IA"
        elif P == 1 and U == 1:
            amode = "IB"

        if wback:
            wback = "!"
        else:
            wback = ""            
                    
        return "LDM%s%s %s%s, %s^" % (condition, amode, Register(Rn), wback, RegisterSet(registers))
        
    def decode_b(self, opcode, encoding):
        """
        A8.8.18
        B
        Branch causes a branch to a target address.
        
        Syntax:
        B{<c>}{<q>} <label>
        """
        props = {}
        ins_id = ARMInstruction.b
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            cond = get_bits(opcode, 11, 8)            
            imm = SignExtend32(get_bits(opcode, 7, 0) << 1, 9)
            
            # if cond == '1110' then UNDEFINED;
            if cond == 14:
                raise UnpredictableInstructionException()
            
            # if cond == '1111' then SEE SVC;
            if cond == 15:
                return self.decode_svc(opcode, encoding)
            
            # if InITBlock() then UNPREDICTABLE;
            if self.InITBlock():
                raise UnpredictableInstructionException()
            
            condition = Condition(cond)
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "B", False, condition, operands, encoding)
                
        elif encoding == eEncodingT2:
            imm = SignExtend32(get_bits(opcode, 11, 0) << 1, 12)
        
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            condition = None
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "B", False, condition, operands, encoding)
            
        elif encoding == eEncodingT3:
            cond = get_bits(opcode, 25, 22)
                        
            S = get_bit(opcode, 26)
            J1 = get_bit(opcode, 13)
            J2 = get_bit(opcode, 11)
            imm6 = get_bits(opcode, 21, 16)
            imm11 = get_bits(opcode, 10, 0)
            
            imm = (S << 20) | (J2 << 19) | (J1 << 18) | (imm6 << 12) | (imm11 << 1)
            imm = SignExtend32(imm, 21)
            
            # if cond<3:1> == '111' then SEE "Related encodings";
            if get_bits(cond, 3, 1) == 0b111:
                raise InstructionNotImplementedException("SEE Related encodings")
            
            # if InITBlock() then UNPREDICTABLE;
            if self.InITBlock():
                raise UnpredictableInstructionException()
            
            condition = Condition(cond)
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "B", False, condition, operands, encoding, ".W")
            
        elif encoding == eEncodingT4:
            S = get_bit(opcode, 26)
            J1 = get_bit(opcode, 13)
            J2 = get_bit(opcode, 11)
            imm10 = get_bits(opcode, 25, 16)
            imm11 = get_bits(opcode, 10, 0)
            
            # I1 = NOT(J1 EOR S); I2 = NOT(J2 EOR S); 
            I1 = ~(J1 ^ S) & 1
            I2 = ~(J2 ^ S) & 1

            imm = (S << 24) | (I1 << 23) | (I2 << 22) | (imm10 << 12) | (imm11 << 1)
            imm = SignExtend32(imm, 25)
            
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            condition = None
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "B", False, condition, operands, encoding, ".W")

        elif encoding == eEncodingA1:
            imm = get_bits(opcode, 23, 0) << 2
            imm = SignExtend32(imm, 26)
            
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "B", False, condition, operands, encoding)            

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
                
        return ins
        
    def decode_bl_immediate(self, opcode, encoding):
        """
        A8.8.25
        BL, BLX (immediate)
        Branch with Link calls a subroutine at a PC-relative address.
        Branch with Link and Exchange Instruction Sets (immediate) calls a subroutine at a PC-relative address, and
        changes instruction set from ARM to Thumb, or from Thumb to ARM.
        
        Syntax:
        BL{X}{<c>}{<q>} <label>

        Unit-test: FAIL
        """
        props = {}
        ins_id = ARMInstruction.bl_immediate
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            S = get_bit(opcode, 26)
            J1 = get_bit(opcode, 13)
            J2 = get_bit(opcode, 11)
            imm10 = get_bits(opcode, 25, 16)
            imm11 = get_bits(opcode, 10, 0)            

            # I1 = NOT(J1 EOR S); I2 = NOT(J2 EOR S); 
            # imm32 = SignExtend(S:I1:I2:imm10:imm11:'0', 32);
            I1 = ~(J1 ^ S) & 1
            I2 = ~(J2 ^ S) & 1

            imm = SignExtend32((S << 24) | (I1 << 23) | (I2 << 22) | (imm10 << 12) | (imm11 << 1), 24)
            
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()
            
            condition = None
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "BL", False, None, operands, encoding)            
            
        elif encoding == eEncodingT2:
            S = get_bit(opcode, 26)
            J1 = get_bit(opcode, 13)
            J2 = get_bit(opcode, 11)
            H = get_bit(opcode, 0)
            imm10H = get_bits(opcode, 25, 16)
            imm10L = get_bits(opcode, 10, 1)
            
            # TODO:
            # if CurrentInstrSet() == InstrSet_ThumbEE || H == '1' then UNDEFINED;
            if H == 1:
                raise UndefinedOpcode()

            # I1 = NOT(J1 EOR S); I2 = NOT(J2 EOR S); 
            # imm32 = SignExtend(S:I1:I2:imm10H:imm10L:'00', 32);
            I1 = ~(J1 ^ S) & 1
            I2 = ~(J2 ^ S) & 1            
            
            imm = SignExtend32((S << 24) | (I1 << 23) | (I2 << 22) | (imm10H << 12) | (imm10L << 2), 25)
            
            # if InITBlock() && !LastInITBlock() then UNPREDICTABLE;
            if self.InITBlock() and not self.LastInITBlock():
                raise UnpredictableInstructionException()

            condition = None
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "BLX", False, None, operands, encoding)            
            
        elif encoding == eEncodingA1:
            imm = SignExtend32(get_bits(opcode, 23, 0) << 2, 26)
            
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "BL", False, condition, operands, encoding)            
            
        elif encoding == eEncodingA2:
            imm = SignExtend32((get_bits(opcode, 23, 0) << 2) | (get_bit(opcode, 24) << 1), 26)
            
            operands = [Jump(imm)]
            ins = Instruction(ins_id, opcode, "BLX", False, condition, operands, encoding)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        return ins
                    
    def decode_svc(self, opcode, encoding):
        """
        SVC (previously SWI)
        Supervisor Call, previously called Software Interrupt, causes a Supervisor Call exception.
        
        Syntax:
        SVC{<c>}{<q>} {#}<imm>
        """
        props = {}
        ins_id = ARMInstruction.svc
        condition = self.decode_condition_field(opcode)
        
        if encoding == eEncodingT1:
            condition = None
            imm = get_bits(opcode, 7, 0)
            
        elif encoding == eEncodingA1:
            imm = get_bits(opcode, 23, 0)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
            
        operands = [Immediate(imm)]
        ins = Instruction(ins_id, opcode, "SVC", False, condition, operands, encoding)
        return ins
    
    def decode_bfc(self, opcode, encoding):
        """
        A8.8.19
        BFC
        Bit Field Clear clears any number of adjacent bits at any position in a register, without affecting the other bits in the
        register.        
        """
        props = {}        
        name = "BFC"
        ins_id = ARMInstruction.bfc
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(17), 3, 4, 2, I(1), 5]
            imm3, Rd, imm2, msbit = decode_opcode(opcode, decode_mask)
            
            # d = UInt(Rd); msbit = UInt(msb); lsbit = UInt(imm3:imm2);
            lsbit = (imm3 << 2) | imm2 
            
            # if d IN {13,15} then UNPREDICTABLE;
            if BadReg(Rd):
                raise UnpredictableInstructionException()
            
        elif encoding == eEncodingA1:
            decode_mask = [4, I(7), 5, 4, 5, I(7)]
            cond, msbit, Rd, lsbit = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
                        
            if Rd == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        # The Immediate value must be positive otherwise we do not make sense.
        if msbit < lsbit:
            raise UnpredictableInstructionException()

        # BFC<c> <Rd>, #<lsb>, #<width>
        operands = [Register(Rd), Immediate(lsbit), Immediate(msbit - lsbit + 1)]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_bfi(self, opcode, encoding):
        """
        A8.8.20
        BFI
        Bit Field Insert copies any number of low order bits from a register into the same number of adjacent bits at any
        position in the destination register.        
        """
        props = {}
        name = "BFI"
        ins_id = ARMInstruction.bfi
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I(1), 3, 4, 2, I(1), 5]
            Rn, imm3, Rd, imm2, msbit = decode_opcode(opcode, decode_mask)

            # if Rn == '1111' then SEE BFC;
            if Rn == 0b1111:
                return self.decode_bfc(opcode, encoding)
            
            # d = UInt(Rd); n = UInt(Rn); msbit = UInt(msb); lsbit = UInt(imm3:imm2);
            lsbit = (imm3 << 2) | imm2 
            
            # if d IN {13,15} || n == 13 then UNPREDICTABLE;
            if BadReg(Rd) or Rn == 13:
                raise UnpredictableInstructionException()
            
        elif encoding == eEncodingA1:
            decode_mask = [4, I(7), 5, 4, 5, I(3), 4]
            cond, msbit, Rd, lsbit, Rn = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            # if Rn == '1111' then SEE BFC;
            if Rn == 0b1111:
                return self.decode_bfc(opcode, encoding)
                        
            if Rd == 15:
                raise UnpredictableInstructionException()
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        # The Immediate value must be positive otherwise we do not make sense.
        if msbit < lsbit:
            raise UnpredictableInstructionException()

        operands = [Register(Rd), Register(Rn), Immediate(lsbit), Immediate(msbit - lsbit + 1)]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_cdp(self, opcode, encoding):
        """
        A8.8.30
        CDP, CDP2
        Coprocessor Data Processing tells a coprocessor to perform an operation that is independent of ARM core registers
        and memory. If no coprocessor can execute the instruction, an Undefined Instruction exception is generated.
        """
        props = {}
        
        ins_id = ARMInstruction.cdp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            name = "CDP"
            decode_mask = [I(8), 4, 4, 4, 4, 3, I(1), 4]
            opc1, CRn, CRd, coproc, opc2, CRm = decode_opcode(opcode, decode_mask)
            
            # if coproc IN "101x" then SEE "Floating-point instructions";
            if coproc in [0b1010, 0b1011]:
                raise RuntimeError("SEE Floating-point instructions")

        elif encoding == eEncodingT2:
            name = "CDP2"
            decode_mask = [I(8), 4, 4, 4, 4, 3, I(1), 4]
            opc1, CRn, CRd, coproc, opc2, CRm = decode_opcode(opcode, decode_mask)

        elif encoding == eEncodingA1:
            name = "CDP"
            decode_mask = [4, I(4), 4, 4, 4, 4, 3, I(1), 4]
            cond, opc1, CRn, CRd, coproc, opc2, CRm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

        elif encoding == eEncodingA2:
            name = "CDP2"
            decode_mask = [I(8), 4, 4, 4, 4, 3, I(1), 4]
            opc1, CRn, CRd, coproc, opc2, CRm = decode_opcode(opcode, decode_mask)

            # if coproc IN "101x" then SEE "Floating-point instructions";
            if coproc in [0b1010, 0b1011]:
                raise RuntimeError("SEE Floating-point instructions")

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [CoprocessorName(coproc), CoprocessorOpCode(opc1), CoprocessorRegister(CRd), CoprocessorRegister(CRn), CoprocessorRegister(CRm), CoprocessorOpCode(opc2)]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_clrex(self, opcode, encoding):
        """
        A8.8.32
        CLREX
        Clear-Exclusive clears the local record of the executing processor that an address has had a request for an exclusive
        access.        
        """
        props = {}
        name = "CLREX"
        ins_id = ARMInstruction.clrex
        setsflags = False
        condition = None
        ins = Instruction(ins_id, opcode, name, setsflags, condition, [], encoding)
        return ins

    def decode_cps(self, opcode, encoding):
        """
        A8.8.40
        CPS
        Change Processor State is a system instruction, see CPS (Thumb) on page B9-1948 and CPS (ARM) on
        page B9-1950.        
        """
        props = {}

        ins_id = ARMInstruction.cps
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(27), 1, I(1), 1, 1 , 1]
            im, a, i, f = decode_opcode(opcode, decode_mask)
                        
            if ((a << 2) | (i << 1) | f) == 0:
                return UnpredictableInstructionException()
            
            enable = im == 0
            disable = im == 1
            changemode = False
            affectA = a == 1
            affectI = i == 0
            affectF = f == 0
            
        elif encoding == eEncodingT2:
            decode_mask = [I(21), 2, 1, 1, 1, 1, 5]
            imod, m, a, i, f, mode = decode_opcode(opcode, decode_mask)

            if imod == 0 and m == 0:
                raise RuntimeError("SEE Hint instructions")
            
            if mode != 0 and m == 0:
                raise UnpredictableInstructionException()
            
            if get_bit(imod, 1) == 1 and (((a << 2) | (i << 1) | f) == 0):
                raise UnpredictableInstructionException() 

            if get_bit(imod, 1) == 0 and (((a << 2) | (i << 1) | f) != 0):
                raise UnpredictableInstructionException() 
            
            enable = imod == 0b10
            disable = imod == 0b11
            changemode = m == 1
            affectA = a == 1
            affectI = i == 1
            affectF = f == 1
            
            if imod == 0b1 or self.InITBlock():
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [I(12), 2, 1, I(8), 1, 1, 1, I(1), 5]
            imod, m, a, i, f, mode = decode_opcode(opcode, decode_mask)
            
            if mode != 0 and m == 0:
                raise UnpredictableInstructionException()
            
            if get_bit(imod, 1) == 1 and (((a << 2) | (i << 1) | f) == 0):
                raise UnpredictableInstructionException()
            
            if get_bit(imod, 1) == 0 and (((a << 2) | (i << 1) | f) != 0):
                raise UnpredictableInstructionException()

            enable = imod == 0b10
            disable = imod == 0b11
            changemode = m == 1
            affectA = a == 1
            affectI = i == 1
            affectF = f == 1
            
            if (imod == 0 and m == 0) or imod == 1:
                raise UnpredictableInstructionException() 

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        # Custom instruction properties.
        props = {}
        props["enable"] = enable
        props["disable"] = disable
        props["changemode"] = changemode
        props["affectA"] = affectA
        props["affectI"] = affectI
        props["affectF"] = affectF

        name = "CPS"
        if a != 0 or i != 0 or f != 0:
            name += "IE" if enable else "ID"
            name += " "
            if a:
                name += "A"
                
            if i:
                name += "I"
                
            if f:
                name += "F"

        operands = [] if encoding == eEncodingT1 else [Immediate(mode)]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_dmb(self, opcode, encoding):
        """
        A8.8.43
        DMB
        Data Memory Barrier is a memory barrier that ensures the ordering of observations of memory accesses, see Data
        Memory Barrier (DMB) on page A3-149.        
        """
        props = {}

        name = "DMB"
        ins_id = ARMInstruction.dmb
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(28), 4]
            option = decode_opcode(opcode, decode_mask)[0]
            operands = [MemoryBarrierOption(option)]

        elif encoding == eEncodingA1:
            decode_mask = [I(28), 4]
            option = decode_opcode(opcode, decode_mask)[0]
            operands = [MemoryBarrierOption(option)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_dsb(self, opcode, encoding):
        """
        A8.8.44
        DSB
        Data Synchronization Barrier is a memory barrier that ensures the completion of memory accesses, see Data
        Synchronization Barrier (DSB) on page A3-150.        
        """
        props = {}
        
        name = "DSB"
        ins_id = ARMInstruction.dsb
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(28), 4]
            option = decode_opcode(opcode, decode_mask)[0]
            operands = [MemoryBarrierOption(option)]

        elif encoding == eEncodingA1:
            decode_mask = [I(28), 4]
            option = decode_opcode(opcode, decode_mask)[0]
            operands = [MemoryBarrierOption(option)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_eret(self, opcode, encoding):
        """
        B9.3.3
        ERET
        When executed in Hyp mode, Exception Return loads the PC from ELR_hyp and loads the CPSR from SPSR_hyp.
        """
        props = {}
        
        name = "ERET"
        ins_id = ARMInstruction.eret
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(24), 8]
            imm8 = decode_opcode(opcode, decode_mask)[0]
            operands = []
            
            # if imm8 != '00000000' then SEE SUBS PC, LR and related instructions;
            if imm8 != 0:
                return self.decode_subs_pc_lr_thumb(opcode, encoding)

        elif encoding == eEncodingA1:
            decode_mask = [4, I(28)]
            cond = decode_opcode(opcode, decode_mask)[0]
            condition = Condition(cond)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_hvc(self, opcode, encoding):
        """
        B9.3.4
        HVC
        Hypervisor Call causes a Hypervisor Call exception. For more information see Hypervisor Call (HVC) exception
        on page B1-1209. Non-secure software executing at PL1 can use this instruction to call the hypervisor to request a
        service. 
        """
        props = {}
        
        name = "HVC"
        ins_id = ARMInstruction.hvc
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I(4), 12]
            imm4, imm12 = decode_opcode(opcode, decode_mask)
            
            # if InITBlock() then UNPREDICTABLE;
            if self.InITBlock():
                raise UnpredictableInstructionException()
            
            # imm16 = imm4:1mm12;
            imm16 = (imm4 << 12) | imm12
            
            operands = [Immediate(imm16)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I(8), 12, I(4), 4]
            cond, imm12, imm4 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            imm16 = (imm12 << 4) | imm4
            operands = [Immediate(imm16)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_isb(self, opcode, encoding):
        """
        A8.8.53
        ISB
        Instruction Synchronization Barrier flushes the pipeline in the processor, so that all instructions following the ISB
        are fetched from cache or memory, after the instruction has been completed.        
        """
        props = {}
        
        name = "ISB"
        ins_id = ARMInstruction.isb
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(28), 4]
            option = decode_opcode(opcode, decode_mask)[0]
            operands = [ISBOption(option)]

        elif encoding == eEncodingA1:
            decode_mask = [I(28), 4]
            option = decode_opcode(opcode, decode_mask)[0]
            operands = [ISBOption(option)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins


    def decode_ldc_immediate(self, opcode, encoding):
        """
        A8.8.55
        LDC, LDC2 (immediate)
        Load Coprocessor loads memory data from a sequence of consecutive memory addresses to a coprocessor. If no
        coprocessor can execute the instruction, an Undefined Instruction exception is generated.        
        """
        props = {}
        ins_id = ARMInstruction.ldc_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            name = "LDC"
            decode_mask = [I(7), 1, 1, 1, 1, I(1), 4, 4, 4, 8]
            p, u, d, w, Rn, CRd, coproc, imm8 = decode_opcode(opcode, decode_mask)
            
        elif encoding == eEncodingT2:
            name = "LDC2"
            decode_mask = [I(7), 1, 1, 1, 1, I(1), 4, 4, 4, 8]
            p, u, d, w, Rn, CRd, coproc, imm8 = decode_opcode(opcode, decode_mask)
                        
        elif encoding == eEncodingA1:
            name = "LDC"
            decode_mask = [4, I(3), 1, 1, 1, 1, I(1), 4, 4, 4, 8]
            cond, p, u, d, w, Rn, CRd, coproc, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            operands = []

        elif encoding == eEncodingA2:
            name = "LDC2"
            decode_mask = [I(7), 1, 1, 1, 1, I(1), 4, 4, 4, 8]
            p, u, d, w, Rn, CRd, coproc, imm8 = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        # if Rn == '1111' then SEE LDC (literal);
        if Rn == 0b1111:
            return self.decode_ldc_literal(opcode, encoding)
        
        # if P == '0' && U == '0' && D == '0' && W == '0' then UNDEFINED
        if p == 0 and u == 0 and d == 0 and w == 0:
            raise UndefinedOpcode()
        
        # if P == '0' && U == '0' && D == '1' && W == '0' then SEE MRRC, MRRC2;
        if p == 0 and u == 0 and d == 1 and w == 0:
            return self.decode_mrc(opcode, encoding)

        # imm32 = ZeroExtend(imm8:'00', 32); index = (P == '1'); add = (U == '1'); wback = (W == '1');
        imm32 = imm8 << 2
        index = p == 1
        add = u == 1
        wback = w == 1

        if not add:
            imm32 *= -1

        if encoding in [eEncodingA1, eEncodingT1]:
            # if coproc IN "101x" then SEE "Advanced SIMD and Floating-point";
            if coproc in [0b1010, 0b1011]:
                raise RuntimeError("SEE Advanced SIMD and Floating-point")
                    
        else:
            # if coproc IN "101x" then UNDEFINED;
            if coproc in [0b1010, 0b1011]:
                raise UndefinedOpcode()

        if p == 1 and w == 0:
            operands = [CoprocessorName(coproc), CoprocessorRegister(CRd), Memory(Register(Rn), Immediate(imm32))]
        
        elif p == 1 and w == 1:
            operands = [CoprocessorName(coproc), CoprocessorRegister(CRd), Memory(Register(Rn), Immediate(imm32), wback=True)]
        
        elif p == 0 and w == 1:
            operands = [CoprocessorName(coproc), CoprocessorRegister(CRd), Memory(Register(Rn)), Immediate(imm32)]

        elif p == 0 and w == 0 and u == 1:
            operands = [CoprocessorName(coproc), CoprocessorRegister(CRd), Memory(Register(Rn)), Immediate(imm8)]
            
        if d == 1:
            name += "L"
        
        props["index"] = index
        props["add"] = add
        props["wback"] = wback

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldc_literal(self, opcode, encoding):
        """
        A8.8.56
        LDC, LDC2 (literal)
        Load Coprocessor loads memory data from a sequence of consecutive memory addresses to a coprocessor. If no
        coprocessor can execute the instruction, an Undefined Instruction exception is generated.        
        """
        props = {}
        
        name = "LDC"
        ins_id = ARMInstruction.ldc_literal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrd_immediate(self, opcode, encoding):
        """
        A8.8.72
        LDRD (immediate)
        Load Register Dual (immediate) calculates an address from a base register value and an immediate offset, loads two
        words from memory, and writes them to two registers. It can use offset, post-indexed, or pre-indexed addressing.
        For information about memory accesses see Memory accesses on page A8-291.        
        """
        props = {}
        
        name = "LDRD"
        ins_id = ARMInstruction.ldrd_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(7), 1, 1, I(1), 1, I(1), 4, 4, 4, 8]
            P, U, W, Rn, Rt, Rt2, imm8 = decode_opcode(opcode, decode_mask)
            
            # if P == '0' && W == '0' then SEE "Related encodings";
            if P == 0 and W == 0:
                raise RuntimeError("SEE Related encodings")
            
            # if Rn == '1111' then SEE LDRD (literal);
            if Rn == 0b1111:
                return self.decode_ldrd_literal(opcode, encoding)
            
            # t = UInt(Rt); t2 = UInt(Rt2); n = UInt(Rn); imm32 = ZeroExtend(imm8:'00', 32);
            imm32 = imm8 << 2
            
            # index = (P == '1'); add = (U == '1'); wback = (W == '1');
            index = P == 1
            add = U == 1
            wback = W == 1
            
            # if wback && (n == t || n == t2) then UNPREDICTABLE;
            if wback and (Rn == Rt or Rn == Rt2):
                raise UnpredictableInstructionException()
            
            # if t IN {13,15} || t2 IN {13,15} || t == t2 then UNPREDICTABLE;    
            if BadReg(Rt) or BadReg(Rt2) or Rt == Rt2:
                raise UnpredictableInstructionException()


        elif encoding == eEncodingA1:
            decode_mask = [4, I(3), 1, 1, I(1), 1, I(1), 4, 4, 4, I(4), 4]
            cond, P, U, W, Rn, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            # if Rn == '1111' then SEE LDRD (literal);
            if Rn == 0b1111:
                return self.decode_ldrd_literal(opcode, encoding)
            
            # if Rt<0> == '1' then UNPREDICTABLE;
            if get_bit(Rt, 0) == 1:
                raise UnpredictableInstructionException()
            
            # t = UInt(Rt); t2 = t+1; n = UInt(Rn); imm32 = ZeroExtend(imm4H:imm4L, 32);
            Rt2 = Rt + 1
            imm32 = (imm4H << 4) | imm4L
            
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            
            # if P == '0' && W == '1' then UNPREDICTABLE;
            if P == 0 and W == 1:
                raise UnpredictableInstructionException()
            
            # if wback && (n == t || n == t2) then UNPREDICTABLE;
            if wback and (Rn == Rt or Rn == Rt2):
                raise UnpredictableInstructionException()
            
            # if t2 == 15 then UNPREDICTABLE;
            if Rt2 == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if not add:
            imm32 *= -1

        if index == True and wback == False:
            operands = [Register(Rt), Register(Rt2), Memory(Register(Rn), Immediate(imm32))]
        
        elif index == True and wback == True:
            operands = [Register(Rt), Register(Rt2), Memory(Register(Rn), Immediate(imm32), wback=True)]
        
        elif index == False and wback == True:
            operands = [Register(Rt), Register(Rt2), Memory(Register(Rn)), Immediate(imm32)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrd_literal(self, opcode, encoding):
        """
        A8.8.73
        LDRD (literal)
        Load Register Dual (literal) calculates an address from the PC value and an immediate offset, loads two words from
        memory, and writes them to two registers. For information about memory accesses see Memory accesses on
        page A8-291.        
        """
        props = {}
        
        name = "LDRD"
        ins_id = ARMInstruction.ldrd_literal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(7), 1, 1, I(1), 1, I(5), 4, 4, 8]
            P, U, W, Rt, Rt2, imm8 = decode_opcode(opcode, decode_mask)
            
            # if P == '0' && W == '0' then SEE "Related encodings";
            if P == 0 and W == 0:
                raise RuntimeError("SEE Related encodings")
            
            # t = UInt(Rt); t2 = UInt(Rt2);
            # imm32 = ZeroExtend(imm8:'00', 32); add = (U == '1');
            imm32 = imm8 << 2
            add = U == 1
            
            # if t IN {13,15} || t2 IN {13,15} || t == t2 then UNPREDICTABLE;
            if BadReg(Rt) or BadReg(Rt2) or Rt == Rt2:
                raise UnpredictableInstructionException()
            
            # if W == '1' then UNPREDICTABLE;
            if W == 1:
                raise UnpredictableInstructionException()    

        elif encoding == eEncodingA1:
            decode_mask = [4, I(4), 1, I(1), I(6), 4, 4, I(4), 4]
            cond, U, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # if Rt<0> == '1' then UNPREDICTABLE;
            if get_bit(Rt, 0) == 1:
                raise UnpredictableInstructionException()
            
            # t = UInt(Rt); t2 = t+1; imm32 = ZeroExtend(imm4H:imm4L, 32);
            Rt2 = Rt + 1
            imm32 = (imm4H << 4) | imm4L
            
            # if t2 == 15 then UNPREDICTABLE;
            if Rt2 == 15:
                raise UnpredictableInstructionException()
            
            add = U == 1

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if not add:
            imm32 *= -1
        
        operands = [Register(Rt), Register(Rt2), Memory(Register(ARMRegister.PC), Immediate(imm32))]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrd_register(self, opcode, encoding):
        """
        A8.8.74
        LDRD (register)
        Load Register Dual (register) calculates an address from a base register value and a register offset, loads two words
        from memory, and writes them to two registers. It can use offset, post-indexed, or pre-indexed addressing. For
        information about memory accesses see Memory accesses on page A8-291.        
        """
        props = {}
        
        name = "LDRD"
        ins_id = ARMInstruction.ldrd_register
        setsflags = False
        condition = None

        if encoding == eEncodingA1:
            decode_mask = [4, I(3), 1, 1, I(1), 1, I(1), 4, 4, I(8), 4]
            cond, P, U, W, Rn, Rt, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # if Rt<0> == '1' then UNPREDICTABLE;
            if get_bit(Rt, 0) == 1:
                raise UnpredictableInstructionException()
            
            # t = UInt(Rt); t2 = t+1; n = UInt(Rn); m = UInt(Rm);
            Rt2 = Rt + 1
            
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            
            # if P == '0' && W == '1' then UNPREDICTABLE;
            if P == 0 and W == 1:
                raise UnpredictableInstructionException()
            
            # if t2 == 15 || m == 15 || m == t || m == t2 then UNPREDICTABLE;
            if Rt2 == 15 or Rm == 15 or Rm == Rt or Rm == Rt2:
                raise UnpredictableInstructionException()
            
            # if wback && (n == 15 || n == t || n == t2) then UNPREDICTABLE;
            if wback and (Rn == 15 or Rn == Rt or Rn == Rt2):
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and wback and Rm == Rn:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if index and wback == False:
            operands = [Register(Rt), Register(Rt2), Memory(Register(Rn), Register(Rm))]
        
        elif index and wback:
            operands = [Register(Rt), Register(Rt2), Memory(Register(Rn), Register(Rm), wback=True)]
        
        elif index == False and wback == True:
            operands = [Register(Rt), Register(Rt2), Memory(Register(Rn)), Register(Rm)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrh_literal(self, opcode, encoding):
        """
        A8.8.81
        LDRH (literal)
        Load Register Halfword (literal) calculates an address from the PC value and an immediate offset, loads a halfword
        from memory, zero-extends it to form a 32-bit word, and writes it to a register. For information about memory
        accesses see Memory accesses on page A8-291.        
        """
        props = {}
        
        name = "LDRH"
        ins_id = ARMInstruction.ldrh_literal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(8), 1, I(7), 4, 12]
            U, Rt, imm12 = decode_opcode(opcode, decode_mask)
            
            # if Rt == '1111' then SEE "Related instructions";
            if Rt == 0b1111:
                raise RuntimeError("SEE Related instructions")
            
            # t = UInt(Rt); imm32 = ZeroExtend(imm12, 32); add = (U == '1');
            imm32 = imm12
            add = U == 1
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I(4), 1, I(7), 4, 4, I(4), 4]
            cond, U, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); imm32 = ZeroExtend(imm4H:imm4L, 32);
            imm32 = (imm4H << 4) | imm4L
            
            # if t == 15 then UNPREDICTABLE;
            if Rt == 15:
                raise UnpredictableInstructionException()

            add = U == 1
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        if not add:
            imm32 *= -1

        operands = [Register(Rt), Memory(Register(ARMRegister.PC), Immediate(imm32))]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrh_register_DUP(self, opcode, encoding):
        """
        A8.8.82
        LDRH (register)
        Load Register Halfword (register) calculates an address from a base register value and an offset register value, loads
        a halfword from memory, zero-extends it to form a 32-bit word, and writes it to a register. The offset register value
        can be shifted left by 0, 1, 2, or 3 bits. 
        """
        props = {}
        
        name = "LDRH"
        ins_id = ARMInstruction.ldrh_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(16), I(7), 3, 3, 3]
            Rm, Rn, Rt = decode_opcode(opcode, decode_mask)

            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm);
            # index = TRUE; add = TRUE; wback = FALSE;
            index = True
            add = True
            wback = False
            
            # (shift_t, shift_n) = (SRType_LSL, 0);
            shift_t, shift_n = SRType_LSL, 0

        elif encoding == eEncodingT2:
            decode_mask = [I(12), 4, 4, I(6), 2, 4]
            Rn, Rt, imm2, Rm = decode_opcode(opcode, decode_mask)
            
            # if Rn == '1111' then SEE LDRH (literal);
            if Rn == 0b1111:
                return self.decode_ldrh_literal_thumb(opcode, encoding)
            
            # if Rt == '1111' then SEE "Related instructions";
            if Rt == 0b1111:
                raise RuntimeError("SEE Related instructions")
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm);
            # index = TRUE; add = TRUE; wback = FALSE;
            index = True
            add = True
            wback = False
            
            # (shift_t, shift_n) = (SRType_LSL, UInt(imm2));
            shift_t, shift_n = SRType_LSL, imm2
            
            # if t == 13 || m IN {13,15} then UNPREDICTABLE;
            if Rt == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I(3), 1, 1, I(1), 1, I(0), 4, 4, I(8), 4]
            cond, P, U, W, Rn, Rt, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # if P == '0' && W == '1' then SEE LDRHT;
            if P == 0 and W == 1:
                return self.decode_ldrht(opcode, encoding)
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm);
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            
            # (shift_t, shift_n) = (SRType_LSL, 0);
            shift_t, shift_n = SRType_LSL, 0
            
            # if t == 15 || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if wback && (n == 15 || n == t) then UNPREDICTABLE;
            if wback and (Rn == 15 or Rn == Rt):
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and wback and Rm == Rn:
                raise UnpredictableInstructionException()
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if index and not wback:
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n))]
        
        elif index and wback:
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n), wback=True)]
        
        elif not index and wback:
            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm)]
            

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrht(self, opcode, encoding):
        """
        A8.8.83
        LDRHT
        Load Register Halfword Unprivileged loads a halfword from memory, zero-extends it to form a 32-bit word, and
        writes it to a register.
        """
        props = {}
        
        name = "LDRHT"
        ins_id = ARMInstruction.ldrht
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, 4, I(4), 8]
            Rn, Rt, imm8 = decode_opcode(opcode, decode_mask)
            
            # if Rn == '1111' then SEE LDRH (literal);
            if Rn == 0b1111:
                return self.decode_ldrh_literal(opcode, encoding)
            
            # t = UInt(Rt); n = UInt(Rn); postindex = FALSE; add = TRUE;
            postindex = False
            add = True
            
            # register_form = FALSE; imm32 = ZeroExtend(imm8, 32);
            register_form = False
            imm32 = imm8
            
            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()
            
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]

        elif encoding == eEncodingA1:
            decode_mask = [4, I(4), 1, I(3), 4, 4, 4, I(4), 4]
            cond, U, Rn, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); n = UInt(Rn); postindex = TRUE; add = (U == '1');
            postindex = True
            add = U == 1
            
            # register_form = FALSE; imm32 = ZeroExtend(imm4H:imm4L, 32);
            register_form = False
            imm32 = (imm4H << 4) | imm4L
            
            # if t == 15 || n == 15 || n == t then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt:
                raise UnpredictableInstructionException()
            
            if not add:
                imm32 *= -1
            
            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]

        elif encoding == eEncodingA2:
            decode_mask = [4, I(4), 1, I(3), 4, 4, I(8), 4]
            cond, U, Rn, Rt, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm); postindex = TRUE;
            postindex = True
            add = U == 1
            
            # register_form = True
            register_form = False
            
            # if t == 15 || n == 15 || n == t then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt or Rm == 15:
                raise UnpredictableInstructionException()
            
            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm)]
        
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrsb_immediate(self, opcode, encoding):
        """
        props = {}
        A8.8.84
        LDRSB (immediate)
        Load Register Signed Byte (immediate) calculates an address from a base register value and an immediate offset,
        loads a byte from memory, sign-extends it to form a 32-bit word, and writes it to a register. It can use offset,
        post-indexed, or pre-indexed addressing.        
        """
        
        name = "LDRSB"
        ins_id = ARMInstruction.ldrsb_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, 4, 12]
            Rn, Rt, imm12 = decode_opcode(opcode, decode_mask)
            
            # if Rt == '1111' then SEE PLI;
            if Rt == 0b1111:
                return self.decode_pli_immediate_literal(opcode, encoding)
            
            # if Rn == '1111' then SEE LDRSB (literal);
            if Rn == 0b1111:
                return self.decode_ldrsb_literal(opcode, encoding)
            
            # t = UInt(Rt); n = UInt(Rn); imm32 = ZeroExtend(imm12, 32);
            imm32 = imm12
            
            # index = TRUE; add = TRUE; wback = FALSE;
            index = True
            add = True
            wback = False
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingT2:
            decode_mask = [I(12), 4, 4, I(1), 1, 1, 1, 8]
            Rn, Rt, P, U, W, imm8 = decode_opcode(opcode, decode_mask)

            # if Rt == '1111' && P == '1' && U == '0' && W == '0' then SEE PLI;
            if Rt == 0b1111 and P == 1 and U == 0 and W == 0:
                return self.decode_pli_immediate_literal(opcode, encoding)
            
            # if Rn == '1111' then SEE LDRSB (literal);
            if Rn == 0b1111:
                return self.decode_ldrsb_literal(opcode, encoding)
            
            # if P == '1' && U == '1' && W == '0' then SEE LDRSBT;
            if P == 1 and U == 1 and W == 0:
                return self.decode_ldrsbt(opcode, encoding)
            
            # if P == '0' && W == '0' then UNDEFINED;
            if P == 0 and W == 0:
                return UndefinedOpcode()
            
            # t = UInt(Rt); n = UInt(Rn); imm32 = ZeroExtend(imm8, 32);
            imm32 = imm8
            
            # index = (P == '1'); add = (U == '1'); wback = (W == '1');
            index = P == 1
            add = U == 1
            wback = W == 1
            
            # if t == 13 || (t == 15 && W == '1') || (wback && n == t) then UNPREDICTABLE;
            if Rt == 13 or (Rt == 15 and W == 1) or (wback and Rn == Rt):
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I3, 1, 1, I1, 1, I1, 4, 4, 4, I4, 4]
            cond, P, U, W, Rn, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # if Rn == '1111' then SEE LDRSB (literal);
            if Rn == 0b1111:
                return self.decode_ldrsb_literal(opcode, encoding)
            
            # if P == '0' && W == '1' then SEE LDRSBT;
            if P == 0 and W == 1:
                return self.decode_ldrsbt(opcode, encoding)
            
            # t = UInt(Rt); n = UInt(Rn); imm32 = ZeroExtend(imm4H:imm4L, 32);
            imm32 = (imm4H << 4) | imm4L
            
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            
            # if t == 15 || (wback && n == t) then UNPREDICTABLE;
            if Rt == 15 or (wback and Rn == Rt):
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if not add:
            imm32 *= -1

        if index and not wback:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
        
        elif index and wback:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=True)]
        
        elif not index and wback:
            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrsb_literal(self, opcode, encoding):
        """
        props = {}
        A8.8.85
        LDRSB (literal)
        Load Register Signed Byte (literal) calculates an address from the PC value and an immediate offset, loads a byte
        from memory, sign-extends it to form a 32-bit word, and writes it to a register.         
        """
        props = {}
        
        name = "LDRSB"
        ins_id = ARMInstruction.ldrsb_literal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I8, 1, I7, 4, 12]
            U, Rt, imm12 = decode_opcode(opcode, decode_mask)
            
            # if Rt == '1111' then SEE PLI;
            if Rt == 0b1111:
                return self.decode_pli_immediate_literal(opcode, encoding)
            
            # t = UInt(Rt); imm32 = ZeroExtend(imm12, 32);
            imm32 = imm12
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I4, 1, I7, 4, 4, I4, 4]
            cond, U, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); imm32 = ZeroExtend(imm4H:imm4L, 32);
            imm32 = (imm4H << 4) | imm4L
            
            # if t == 15 then UNPREDICTABLE;
            if Rt == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        add = U == 1
        if not add:
            imm32 *= -1

        operands = [Register(Rt), Memory(Register(ARMRegister.PC), Immediate(imm32))]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrsb_register(self, opcode, encoding):
        """
        A8.8.86
        LDRSB (register)
        Load Register Signed Byte (register) calculates an address from a base register value and an offset register value,
        loads a byte from memory, sign-extends it to form a 32-bit word, and writes it to a register. The offset register value
        can be shifted left by 0, 1, 2, or 3 bits.        
        """
        props = {}
        
        name = "LDRSB"
        ins_id = ARMInstruction.ldrsb_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(23), 3, 3, 3]
            Rm, Rn, Rt = decode_opcode(opcode, decode_mask)
            
            # index = TRUE; add = TRUE; wback = FALSE;
            index = True
            add = True
            wback = False
            
            # (shift_t, shift_n) = (SRType_LSL, 0);
            shift_t, shift_n = SRType_LSL, 0

        elif encoding == eEncodingT2:
            decode_mask = [I(12), 4, 4, I6, 2, 4]
            Rn, Rt, imm2, Rm = decode_opcode(opcode, decode_mask)
            
            # if Rt == '1111' then SEE PLI;
            if Rt == 0b1111:
                return self.decode_pli_register(opcode, encoding)
            
            # if Rn == '1111' then SEE LDRSB (literal);
            if Rn == 0b1111:
                return self.decode_ldrsb_literal(opcode, encoding)
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm);
            # index = TRUE; add = TRUE; wback = FALSE;
            index = True
            add = True
            wback = False
            
            # (shift_t, shift_n) = (SRType_LSL, UInt(imm2));
            shift_t, shift_n = SRType_LSL, imm2
            
            # if t == 13 || m IN {13,15} then UNPREDICTABLE;
            if Rt == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I3, 1, 1, I1, 1, I1, 4, 4, I8, 4]
            cond, P, U, W, Rn, Rt, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # if P == '0' && W == '1' then SEE LDRSBT;
            if P == 0 and W == 1:
                return self.decode_ldrsbt(opcode, eEncodingA2)
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm);
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            
            # (shift_t, shift_n) = (SRType_LSL, 0);
            shift_t, shift_n = SRType_LSL, 0
            
            # if t == 15 || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if wback && (n == 15 || n == t) then UNPREDICTABLE;
            if wback and (Rn == 15 or Rn == Rt):
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and wback and Rm == Rn:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if index and not wback:
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n))]
        
        elif index and wback:
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), wback=True)]
        
        elif not index and wback:
            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrsbt(self, opcode, encoding):
        """
        A8.8.87
        LDRSBT
        Load Register Signed Byte Unprivileged loads a byte from memory, sign-extends it to form a 32-bit word, and
        writes it to a register.         
        """
        props = {}
        
        name = "LDRSBT"
        ins_id = ARMInstruction.ldrsbt
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, 4, I4, 8]
            Rn, Rt, imm8 = decode_opcode(opcode, decode_mask)
            
            # if Rn == '1111' then SEE LDRSB (literal);
            if Rn == 0b1111:
                return self.decode_ldrsb_literal(opcode, encoding)
            
            # t = UInt(Rt); n = UInt(Rn); postindex = FALSE; add = TRUE;
            postindex = False
            add = True
            
            # register_form = FALSE; imm32 = ZeroExtend(imm8, 32);
            register_form = False
            imm32 = imm8
            
            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()
            
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]

        elif encoding == eEncodingA1:
            decode_mask = [4, I4, 1, I3, 4, 4, 4, I4, 4]
            cond, U, Rn, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); n = UInt(Rn); postindex = TRUE; add = (U == '1');
            postindex = True
            add = U == 1
            
            # register_form = FALSE; imm32 = ZeroExtend(imm4H:imm4L, 32);
            register_form = False
            imm32 = (imm4H << 4) | imm4L
            
            # if t == 15 || n == 15 || n == t then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt:
                raise UnpredictableInstructionException()

            if not add:
                imm32 *= -1

            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]

        elif encoding == eEncodingA2:
            decode_mask = [4, I4, 1, I3, 4, 4, I8, 4]
            cond, U, Rn, Rt, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm); postindex = TRUE;
            postindex = True
            
            # register_form = TRUE;
            register_form = True
            
            # if t == 15 || n == 15 || n == t || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt or Rm == 15:
                raise UnpredictableInstructionException()
            
            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrsh_immediate(self, opcode, encoding):
        """
        A8.8.88
        LDRSH (immediate)
        Load Register Signed Halfword (immediate) calculates an address from a base register value and an immediate
        offset, loads a halfword from memory, sign-extends it to form a 32-bit word, and writes it to a register. It can use
        offset, post-indexed, or pre-indexed addressing.         
        """
        props = {}
        
        name = "LDRSH"
        ins_id = ARMInstruction.ldrsh_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, 4, 12]
            Rn, Rt, imm12 = decode_opcode(opcode, decode_mask)
            
            # if Rn == '1111' then SEE LDRSH (literal);
            if Rn == 0b1111:
                return self.decode_ldrsh_literal(opcode, encoding)
            
            # if Rt == '1111' then SEE "Related instructions";
            if Rt == 0b1111:
                raise RuntimeError("SEE Related instructions")
            
            # t = UInt(Rt); n = UInt(Rn); imm32 = ZeroExtend(imm12, 32);
            imm32 = imm12
            
            # index = TRUE; add = TRUE; wback = FALSE;
            index = True
            add = True
            wback = False
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingT2:
            decode_mask = [I(12), 4, 4, I1, 1, 1, 1, 8]
            Rn, Rt, P, U, W, imm8 = decode_opcode(opcode, decode_mask)
            
            # if Rn == '1111' then SEE LDRSH (literal);
            if Rn == 0b1111:
                return self.decode_ldrsh_literal(opcode, encoding)
            
            # if Rt == '1111' && P == '1' && U == '0' && W == '0' then SEE "Related instructions";
            if Rt == 0b1111 and P == 1 and U == 0 and W == 0:
                raise RuntimeError("SEE Related instructions")
            
            # if P == '1' && U == '1' && W == '0' then SEE LDRSHT;
            if P == 1 and U == 1 and W == 0:
                return self.decode_ldrsht(opcode, encoding)
            
            # if P == '0' && W == '0' then UNDEFINED;
            if P == 0 and W == 0:
                raise UndefinedOpcode()
            
            # t = UInt(Rt); n = UInt(Rn); imm32 = ZeroExtend(imm8, 32);
            imm32 = imm8
            
            # index = (P == '1'); add = (U == '1'); wback = (W == '1');
            index = P == 1
            add = U == 1
            wback = W == 1
            
            # if t == 13 || (t == 15 && W == '1') || (wback && n == t) then UNPREDICTABLE;
            if Rt == 13 or (Rt == 15 and W == 1) or (wback and Rn == Rt):
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I3, 1, 1, I1, 1, I1, 4, 4, 4, I4, 4]
            cond, P, U, W, Rn, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # if Rn == '1111' then SEE LDRSH (literal);
            if Rn == 0b1111:
                return self.decode_ldrsh_literal(opcode, encoding)
            
            # if P == '0' && W == '1' then SEE LDRSHT;
            if P == 0 and W == 1:
                return self.decode_ldrsht(opcode, encoding)
            
            # t = UInt(Rt); n = UInt(Rn); imm32 = ZeroExtend(imm4H:imm4L, 32);
            imm32 = (imm4H << 4) | imm4L
            
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1
            add = U == 1
            wback = P == 0 or W == 1
            
            # if t == 15 || (wback && n == t) then UNPREDICTABLE;
            if Rt == 15 or (wback and Rn == Rt):
                raise UnpredictableInstructionException()            
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if not add:
            imm32 *= -1

        if index and not wback:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
        
        elif index and wback:
            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32), wback=True)]
        
        elif not index and wback:
            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrsh_literal(self, opcode, encoding):
        """
        A8.8.89
        LDRSH (literal)
        Load Register Signed Halfword (literal) calculates an address from the PC value and an immediate offset, loads a
        halfword from memory, sign-extends it to form a 32-bit word, and writes it to a register.        
        """
        props = {}
        
        name = "LDRSH"
        ins_id = ARMInstruction.ldrsh_literal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I8, 1, I7, 4, 12]
            U, Rt, imm12 = decode_opcode(opcode, decode_mask)
            
            # if Rt == '1111' then SEE "Related instructions";
            if Rt == 0b1111:
                raise RuntimeError("SEE Related instructions")
            
            # t = UInt(Rt); imm32 = ZeroExtend(imm12, 32); add = (U == '1');
            imm32 = imm12
            add = U == 1
            
            # if t == 13 then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I4, 1, I7, 4, 4, I4, 4]
            cond, U, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); imm32 = ZeroExtend(imm4H:imm4L, 32);
            imm32 = (imm4H << 4) | imm4L
            add = U == 1
            
            # if t == 15 then UNPREDICTABLE;
            if Rt == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
    
        if not add:
            imm32 *= -1
            
        operands = [Register(Rt), Memory(Register(ARMRegister.PC), Immediate(imm32))]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrsh_register(self, opcode, encoding):
        """
        A8.8.90
        LDRSH (register)
        Load Register Signed Halfword (register) calculates an address from a base register value and an offset register
        value, loads a halfword from memory, sign-extends it to form a 32-bit word, and writes it to a register. The offset
        register value can be shifted left by 0, 1, 2, or 3 bits.         
        """
        props = {}
        
        name = "LDRSH"
        ins_id = ARMInstruction.ldrsh_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(23), 3, 3, 3]
            Rm, Rn, Rt = decode_opcode(opcode, decode_mask)

            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm);
            # index = TRUE; add = TRUE; wback = FALSE;
            index = True
            add = True
            wback = False
            
            # (shift_t, shift_n) = (SRType_LSL, 0);
            shift_t, shift_n = SRType_LSL, 0

        elif encoding == eEncodingT2:
            decode_mask = [I(12), 4, 4, I6, 2, 4]
            Rn, Rt, imm2, Rm = decode_opcode(opcode, decode_mask)
            
            # if Rn == '1111' then SEE LDRSH (literal);
            if Rn == 0b1111:
                return self.decode_ldrsh_literal(opcode, encoding)
            
            # if Rt == '1111' then SEE "Related instructions";
            if Rt == 0b1111:
                raise RuntimeError("SEE Related instructions")
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm);
            # index = TRUE; add = TRUE; wback = FALSE;
            index = True
            add = True
            wback = False
            
            # (shift_t, shift_n) = (SRType_LSL, UInt(imm2));
            shift_t, shift_n = SRType_LSL, imm2
            
            # if t == 13 || m IN {13,15} then UNPREDICTABLE;
            if Rt == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I3, 1, 1, I1, 1, I1, 4, 4, I8, 4]
            cond, P, U, W, Rn, Rt, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # if P == '0' && W == '1' then SEE LDRSHT;
            if P == 0 and W == 1:
                return self.decode_ldrsht(opcode, eEncodingA2)
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm);
            # index = (P == '1'); add = (U == '1'); wback = (P == '0') || (W == '1');
            index = P == 1 
            add = U == 1
            wback = P == 0 or W == 1
            
            # (shift_t, shift_n) = (SRType_LSL, 0);
            shift_t, shift_n = SRType_LSL, 0
            
            # if t == 15 || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rm == 15:
                raise UnpredictableInstructionException()
            
            # if wback && (n == 15 || n == t) then UNPREDICTABLE;
            if wback and (Rn == 15 or Rn == Rt):
                raise UnpredictableInstructionException()
            
            # if ArchVersion() < 6 && wback && m == n then UNPREDICTABLE;
            if self.ArchVersion() < 6 and wback and Rm == Rn:
                raise UnpredictableInstructionException()
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if index and not wback:
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm))]
        
        elif index and wback:
            operands = [Register(Rt), Memory(Register(Rn), Register(Rm), wback=True)]
        
        elif not index and wback:
            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ldrsht(self, opcode, encoding):
        """
        A8.8.91
        LDRSHT
        Load Register Signed Halfword Unprivileged loads a halfword from memory, sign-extends it to form a 32-bit word,
        and writes it to a register.         
        """
        props = {}
        
        name = "LDRSHT"
        ins_id = ARMInstruction.ldrsht
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, 4, I4, 8]
            Rn, Rt, imm8 = decode_opcode(opcode, decode_mask)
            
            # if Rn == '1111' then SEE LDRSH (literal);
            if Rn == 0b1111:
                return self.decode_ldrsh_literal(opcode, encoding)

            # t = UInt(Rt); n = UInt(Rn); postindex = FALSE; add = TRUE;
            postindex = False
            add = True

            # register_form = FALSE; imm32 = ZeroExtend(imm8, 32);
            register_form = False
            imm32 = imm8

            # if t IN {13,15} then UNPREDICTABLE;
            if BadReg(Rt):
                raise UnpredictableInstructionException()

            operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]

        elif encoding == eEncodingA1:
            decode_mask = [4, I4, 1, I3, 4, 4, 4, I4, 4]
            cond, U, Rn, Rt, imm4H, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); n = UInt(Rn); postindex = TRUE; add = (U == '1');
            postindex = True
            add = U == 1

            # register_form = FALSE; imm32 = ZeroExtend(imm4H:imm4L, 32);
            register_form = False
            imm32 = (imm4H << 4) | imm4L

            # if t == 15 || n == 15 || n == t then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt:
                raise UnpredictableInstructionException()

            if not add:
                imm32 *= -1

            operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]

        elif encoding == eEncodingA2:
            decode_mask = [4, I4, 1, I3, 4, 4, I8, 4]
            cond, U, Rn, Rt, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            
            # t = UInt(Rt); n = UInt(Rn); m = UInt(Rm); postindex = TRUE;
            postindex = True

            # register_form = TRUE;
            register_form = True
            
            add = U == 1

            # if t == 15 || n == 15 || n == t || m == 15 then UNPREDICTABLE;
            if Rt == 15 or Rn == 15 or Rn == Rt or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rt), Memory(Register(Rn)), Register(Rm)]


        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_enterx_leavex(self, opcode, encoding):
        """
        A8.8.93
        LEAVEX
        LEAVEX causes a change from ThumbEE to Thumb state, or has no effect in Thumb state. 
        ENTERX causes a change from Thumb state to ThumbEE state, or has no effect in ThumbEE state.
        """
        props = {}
        
        ins_id = ARMInstruction.enterx_leavex
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(27), 1, 4]
            J = decode_opcode(opcode, decode_mask)[0]

            name = "ENTERX" if J == 1 else "LEAVEX"
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_mcr(self, opcode, encoding):
        """
        A8.8.98
        MCR, MCR2
        Move to Coprocessor from ARM core register passes the value of an ARM core register to a coprocessor. If no
        coprocessor can execute the instruction, an Undefined Instruction exception is generated.        
        """
        props = {}
        
        name = "MCR"
        ins_id = ARMInstruction.mcr
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_mcrr(self, opcode, encoding):
        """
        A8.8.99
        MCRR, MCRR2
        Move to Coprocessor from two ARM core registers passes the values of two ARM core registers to a coprocessor.
        If no coprocessor can execute the instruction, an Undefined Instruction exception is generated.        
        """
        props = {}
        
        name = "MCRR"
        ins_id = ARMInstruction.mcrr
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_mrs(self, opcode, encoding):
        """
        A8.8.109
        MRS
        Move to Register from Special register moves the value from the APSR into a general-purpose register.        
        """
        props = {}
        
        name = "MRS"
        ins_id = ARMInstruction.mrs
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_mrs_banked_register(self, opcode, encoding):
        """
        A8.8.110
        MRS (Banked register)
        Move to Register from Banked or Special register is a system instruction, see MRS (Banked register) on
        page B9-1960.        
        """
        props = {}
        
        name = "MRS"
        ins_id = ARMInstruction.mrs_banked_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_msr_immediate(self, opcode, encoding):
        """
        A8.8.111
        MSR (immediate)
        Move immediate value to Special register moves selected bits of an immediate value to the corresponding bits in
        the APSR.        
        """
        props = {}
        
        name = "MSR"
        ins_id = ARMInstruction.msr_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_msr_register(self, opcode, encoding):
        """
        A8.8.112
        MSR (register)
        Move to Special register from ARM core register moves selected bits of an ARM core register to the APSR.        
        """
        props = {}
        
        name = "MSR"
        ins_id = ARMInstruction.msr_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_msr_banked_register(self, opcode, encoding):
        """
        A8.8.113
        MSR (Banked register)
        Move to Banked or Special register from ARM core register is a system instruction, see MSR (Banked register) on
        page B9-1964.        
        """
        props = {}
        
        name = "MSR"
        ins_id = ARMInstruction.msr_banked_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_orn_immediate(self, opcode, encoding):
        """
        A8.8.120
        ORN (immediate)
        Bitwise OR NOT (immediate) performs a bitwise (inclusive) OR of a register value and the complement of an
        immediate value, and writes the result to the destination register. It can optionally update the condition flags based
        on the result.        
        """
        props = {}
        
        name = "ORN"
        ins_id = ARMInstruction.orn_immediate
        setsflags = False
        condition = None

        qualifiers = ""
        if encoding == eEncodingT1:
            decode_mask = [I5, 1, I5, 1, 4, I1, 3, 4, 8]
            i, S, Rn, imm3, Rd, imm8 = decode_opcode(opcode, decode_mask)
            if Rn == 0b1111:
                return self.decode_mvn_immediate(opcode, encoding)

            setsflags = S == 1
            imm32, _ = ThumbExpandImm_C(opcode, 0)

            if BadReg(Rd) or Rn == 13:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Immediate(imm32)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_orn_register(self, opcode, encoding):
        """
        A8.8.121
        ORN (register)
        Bitwise OR NOT (register) performs a bitwise (inclusive) OR of a register value and the complement of an
        optionally-shifted register value, and writes the result to the destination register. It can optionally update the
        condition flags based on the result.        
        """
        props = {}
        
        name = "ORN"
        ins_id = ARMInstruction.orn_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(11), 1, 4, I1, 3, 4, 2, 2, 4]
            S, Rn, imm3, Rd, imm2, type_, Rm = decode_opcode(opcode, decode_mask)
            if Rn == 0b1111:
                return self.decode_mvn_register(opcode, encoding)

            setsflags = S == 1
            shift_t, shift_n = DecodeImmShiftThumb(opcode)
            if BadReg(Rd) or Rn == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_pkh(self, opcode, encoding):
        """
        A8.8.125
        PKH
        Pack Halfword combines one halfword of its first operand with the other halfword of its shifted second operand.        
        """
        props = {}
        
        name = "PKH"
        ins_id = ARMInstruction.pkh
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_pld_immediate(self, opcode, encoding):
        """
        A8.8.126
        PLD, PLDW (immediate)
        Preload Data signals the memory system that data memory accesses from a specified address are likely in the near
        future. The memory system can respond by taking actions that are expected to speed up the memory accesses when
        they do occur, such as pre-loading the cache line containing the specified address into the data cache.         
        """
        props = {}
        
        name = "PLD"
        ins_id = ARMInstruction.pld_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_pld_literal(self, opcode, encoding):
        """
        A8.8.127
        PLD (literal)
        Preload Data signals the memory system that data memory accesses from a specified address are likely in the near
        future. The memory system can respond by taking actions that are expected to speed up the memory accesses when
        they do occur, such as pre-loading the cache line containing the specified address into the data cache        
        """
        props = {}
        
        name = "PLD"
        ins_id = ARMInstruction.pld_literal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_pld_register(self, opcode, encoding):
        """
        A8.8.128
        PLD, PLDW (register)
        Preload Data signals the memory system that data memory accesses from a specified address are likely in the near
        future. The memory system can respond by taking actions that are expected to speed up the memory accesses when
        they do occur, such as pre-loading the cache line containing the specified address into the data cache.        
        """
        props = {}
        
        name = "PLD"
        ins_id = ARMInstruction.pld_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_pli_immediate_literal(self, opcode, encoding):
        """
        A8.8.129
        PLI (immediate, literal)
        Preload Instruction signals the memory system that instruction memory accesses from a specified address are likely
        in the near future. The memory system can respond by taking actions that are expected to speed up the memory
        accesses when they do occur, such as pre-loading the cache line containing the specified address into the instruction
        cache.         
        """
        props = {}
        
        name = "PLI"
        ins_id = ARMInstruction.pli_immediate_literal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT3:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_pli_register(self, opcode, encoding):
        """
        A8.8.130
        PLI (register)
        Preload Instruction signals the memory system that instruction memory accesses from a specified address are likely
        in the near future. The memory system can respond by taking actions that are expected to speed up the memory
        accesses when they do occur, such as pre-loading the cache line containing the specified address into the instruction
        cache.         
        """
        props = {}
        
        name = "PLI"
        ins_id = ARMInstruction.pli_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qadd(self, opcode, encoding):
        """
        A8.8.134
        QADD
        Saturating Add adds two register values, saturates the result to the 32-bit signed integer range, and
        writes the result to the destination register. If saturation occurs, it sets the Q flag in the APSR.        
        """
        props = {}
        
        name = "QADD"
        ins_id = ARMInstruction.qadd
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qadd16(self, opcode, encoding):
        """
        A8.8.135
        QADD16
        Saturating Add 16 performs two 16-bit integer additions, saturates the results to the 16-bit signed integer range
        and writes the results to the destination register.
        """
        props = {}
        
        name = "QADD16"
        ins_id = ARMInstruction.qadd16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qadd8(self, opcode, encoding):
        """
        A8.8.136
        QADD8
        Saturating Add 8 performs four 8-bit integer additions, saturates the results to the 8-bit signed integer range
        and writes the results to the destination register.        
        """
        props = {}
        
        name = "QADD8"
        ins_id = ARMInstruction.qadd8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qasx(self, opcode, encoding):
        """
        A8.8.137
        QASX
        Saturating Add and Subtract with Exchange exchanges the two halfwords of the second operand, performs one
        16-bit integer addition and one 16-bit subtraction, saturates the results to the 16-bit signed integer range
        215 x 215  1 and writes the results to the destination register.        
        """
        props = {}
        
        name = "QASX"
        ins_id = ARMInstruction.qasx
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qdadd(self, opcode, encoding):
        """
        A8.8.138
        QDADD
        Saturating Double and Add adds a doubled register value to another register value, and writes the result to the
        destination register. Both the doubling and the addition have their results saturated to the 32-bit signed integer range
        If saturation occurs in either operation, it sets the Q flag in the APSR.        
        """
        props = {}
        
        name = "QDADD"
        ins_id = ARMInstruction.qdadd
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qdsub(self, opcode, encoding):
        """
        A8.8.139
        QDSUB
        Saturating Double and Subtract subtracts a doubled register value from another register value, and writes the result
        to the destination register. Both the doubling and the subtraction have their results saturated to the 32-bit signed
        integer range. If saturation occurs in either operation, it sets the Q flag in the APSR.        
        """
        props = {}
        
        name = "QDSUB"
        ins_id = ARMInstruction.qdsub
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qsax(self, opcode, encoding):
        """
        A8.8.140
        QSAX
        Saturating Subtract and Add with Exchange exchanges the two halfwords of the second operand, performs one
        16-bit integer subtraction and one 16-bit addition, saturates the results to the 16-bit signed integer range,
        and writes the results to the destination register.        
        """
        props = {}
        
        name = "QSAX"
        ins_id = ARMInstruction.qsax
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qsub(self, opcode, encoding):
        """
        A8.8.141
        QSUB
        Saturating Subtract subtracts one register value from another register value, saturates the result to the 32-bit signed
        integer range, and writes the result to the destination register. If saturation occurs, it sets the Q
        flag in the APSR.        
        """
        props = {}
        
        name = "QSUB"
        ins_id = ARMInstruction.qsub
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qsub16(self, opcode, encoding):
        """
        A8.8.142
        QSUB16
        Saturating Subtract 16 performs two 16-bit integer subtractions, saturates the results to the 16-bit signed integer
        range, and writes the results to the destination register.        
        """
        props = {}
        
        name = "QSUB16"
        ins_id = ARMInstruction.qsub16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_qsub8(self, opcode, encoding):
        """
        A8.8.143
        QSUB8
        Saturating Subtract 8 performs four 8-bit integer subtractions, saturates the results to the 8-bit signed integer range
        and writes the results to the destination register.        
        """
        props = {}
        
        name = "QSUB8"
        ins_id = ARMInstruction.qsub8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_rbit(self, opcode, encoding):
        """
        A8.8.144
        RBIT
        Reverse Bits reverses the bit order in a 32-bit register.
        """
        props = {}
        
        name = "RBIT"
        ins_id = ARMInstruction.rbit
        setsflags = False
        condition = None
        
        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I4, 4, I4, 4]
            Rm1, Rd, Rm2 = decode_opcode(opcode, decode_mask)
            if Rm1 != Rm2:
                raise UnpredictableInstructionException()

            if BadReg(Rd) or BadReg(Rm1):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rm1)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I(12), 4, I8, 4]
            cond, Rd, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rm)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_rev(self, opcode, encoding):
        """
        A8.8.145
        REV
        Byte-Reverse Word reverses the byte order in a 32-bit register.        
        """
        props = {}
        
        name = "REV"
        ins_id = ARMInstruction.rev
        setsflags = False
        condition = None
        qualifier = ""

        if encoding == eEncodingT1:
            decode_mask = [I(26), 3, 3]
            Rm, Rd = decode_opcode(opcode, decode_mask)
            operands = [Register(Rd), Register(Rm)]

        elif encoding == eEncodingT2:
            decode_mask = [I(12), 4, I4, 4, I4, 4]
            Rm1, Rd, Rm2 = decode_opcode(opcode, decode_mask)
            qualifier = ".W"

            if Rm1 != Rm2:
                raise UnpredictableInstructionException()

            if BadReg(Rd) or BadReg(Rm1):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rm1)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I(12), 4, I8, 4]
            cond, Rd, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rm)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_rev16(self, opcode, encoding):
        """
        A8.8.146
        REV16
        Byte-Reverse Packed Halfword reverses the byte order in each16-bit halfword of a 32-bit register.        
        """
        props = {}
        
        name = "REV16"
        ins_id = ARMInstruction.rev16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_revsh(self, opcode, encoding):
        """
        A8.8.147
        REVSH
        Byte-Reverse Signed Halfword reverses the byte order in the lower 16-bit halfword of a 32-bit register, and
        sign-extends the result to 32 bits.        
        """
        props = {}
        
        name = "REVSH"
        ins_id = ARMInstruction.revsh
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sadd16(self, opcode, encoding):
        """
        A8.8.158
        SADD16
        Signed Add 16 performs two 16-bit signed integer additions, and writes the results to the destination register. It sets
        the APSR.GE bits according to the results of the additions.        
        """
        props = {}
        
        name = "SADD16"
        ins_id = ARMInstruction.sadd16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sadd8(self, opcode, encoding):
        """
        A8.8.159
        SADD8
        Signed Add 8 performs four 8-bit signed integer additions, and writes the results to the destination register. It sets
        the APSR.GE bits according to the results of the additions.        
        """
        props = {}
        
        name = "SADD8"
        ins_id = ARMInstruction.sadd8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sasx(self, opcode, encoding):
        """
        A8.8.160
        SASX
        Signed Add and Subtract with Exchange exchanges the two halfwords of the second operand, performs one 16-bit
        integer addition and one 16-bit subtraction, and writes the results to the destination register. It sets the APSR.GE
        bits according to the results.        
        """
        props = {}
        
        name = "SASX"
        ins_id = ARMInstruction.sasx
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sbfx(self, opcode, encoding):
        """
        A8.8.164
        SBFX
        Signed Bit Field Extract extracts any number of adjacent bits at any position from a register, sign-extends them to
        32 bits, and writes the result to the destination register.        
        """
        props = {}
        
        name = "SBFX"
        ins_id = ARMInstruction.sbfx
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I1, 3, 4, 2, I1, 5]
            Rn, imm3, Rd, imm2, widthm1 = decode_opcode(opcode, decode_mask)
            lsbit = (imm3 << 2) | imm2
            widthminus1 = widthm1

            if BadReg(Rd) or BadReg(Rn):
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I7, 5, 4, 5, I3, 4]
            widthm1, Rd, lsb, Rn = decode_opcode(opcode, decode_mask)
            lsbit = lsb
            widthminus1 = widthm1

            if Rd == 15 or Rn == 15:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rd), Register(Rn), Immediate(lsbit), Immediate(widthminus1 + 1)]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sdiv(self, opcode, encoding):
        """
        A8.8.165
        SDIV
        Signed Divide divides a 32-bit signed integer register value by a 32-bit signed integer register value, and writes the
        result to the destination register. The condition flags are not affected.        
        """
        props = {}
        
        name = "SDIV"
        ins_id = ARMInstruction.sdiv
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sel(self, opcode, encoding):
        """
        A8.8.166
        SEL
        Select Bytes selects each byte of its result from either its first operand or its second operand, according to the values
        of the GE flags.        
        """
        props = {}
        
        name = "SEL"
        ins_id = ARMInstruction.sel
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_setend(self, opcode, encoding):
        """
        A8.8.167
        SETEND
        Set Endianness writes a new value to ENDIANSTATE.        
        """
        props = {}
        
        name = "SETEND"
        ins_id = ARMInstruction.setend
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_shadd16(self, opcode, encoding):
        """
        A8.8.169
        SHADD16
        Signed Halving Add 16 performs two signed 16-bit integer additions, halves the results, and writes the results to the
        destination register.        
        """
        props = {}
        
        name = "SHADD16"
        ins_id = ARMInstruction.shadd16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_shadd8(self, opcode, encoding):
        """
        A8.8.170
        SHADD8
        Signed Halving Add 8 performs four signed 8-bit integer additions, halves the results, and writes the results to the
        destination register.        
        """
        props = {}
        
        name = "SHADD8"
        ins_id = ARMInstruction.shadd8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_shasx(self, opcode, encoding):
        """
        A8.8.171
        SHASX
        Signed Halving Add and Subtract with Exchange exchanges the two halfwords of the second operand, performs one
        signed 16-bit integer addition and one signed 16-bit subtraction, halves the results, and writes the results to the
        destination register.        
        """
        props = {}
        
        name = "SHASX"
        ins_id = ARMInstruction.shasx
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_shsax(self, opcode, encoding):
        """
        A8.8.172
        SHSAX
        Signed Halving Subtract and Add with Exchange exchanges the two halfwords of the second operand, performs one
        signed 16-bit integer subtraction and one signed 16-bit addition, halves the results, and writes the results to the
        destination register.        
        """
        props = {}
        
        name = "SHSAX"
        ins_id = ARMInstruction.shsax
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_shsub16(self, opcode, encoding):
        """
        A8.8.173
        SHSUB16
        Signed Halving Subtract 16 performs two signed 16-bit integer subtractions, halves the results, and writes the results
        to the destination register.        
        """
        props = {}
        
        name = "SHSUB16"
        ins_id = ARMInstruction.shsub16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_shsub8(self, opcode, encoding):
        """
        A8.8.174
        SHSUB8
        Signed Halving Subtract 8 performs four signed 8-bit integer subtractions, halves the results, and writes the results
        to the destination register.        
        """
        props = {}
        
        name = "SHSUB8"
        ins_id = ARMInstruction.shsub8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smlad(self, opcode, encoding):
        """
        A8.8.177
        SMLAD
        Signed Multiply Accumulate Dual performs two signed 16x16-bit multiplications. It adds the products to a 32bit
        accumulate operand.        
        """
        props = {}
        
        name = "SMLAD"
        ins_id = ARMInstruction.smlad
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smlal(self, opcode, encoding):
        """
        A8.8.178
        SMLAL
        Signed Multiply Accumulate Long multiplies two signed 32-bit values to produce a 64-bit value, and accumulates
        this with a 64-bit value.        
        """
        props = {}
        name = "SMLAL"
        ins_id = ARMInstruction.smlal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smlald(self, opcode, encoding):
        """
        A8.8.180
        SMLALD
        Signed Multiply Accumulate Long Dual performs two signed 16 x 16-bit multiplications. It adds the products to a
        64-bit accumulate operand.        
        """
        props = {}
        
        name = "SMLALD"
        ins_id = ARMInstruction.smlald
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smlsd(self, opcode, encoding):
        """
        A8.8.182
        SMLSD
        Signed Multiply Subtract Dual performs two signed 16 x 16-bit multiplications. It adds the difference of the
        products to a 32-bit accumulate operand.    
        """
        props = {}
        
        name = "SMLSD"
        ins_id = ARMInstruction.smlsd
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smlsld(self, opcode, encoding):
        """
        A8.8.183
        SMLSLD
        Signed Multiply Subtract Long Dual performs two signed 16 x 16-bit multiplications. It adds the difference of the
        products to a 64-bit accumulate operand.        
        """
        props = {}
        
        name = "SMLSLD"
        ins_id = ARMInstruction.smlsld
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smmla(self, opcode, encoding):
        """
        A8.8.184
        SMMLA
        Signed Most Significant Word Multiply Accumulate multiplies two signed 32-bit values, extracts the most
        significant 32 bits of the result, and adds an accumulate value.        
        """
        props = {}
        
        name = "SMMLA"
        ins_id = ARMInstruction.smmla
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smmls(self, opcode, encoding):
        """
        A8.8.185
        SMMLS
        Signed Most Significant Word Multiply Subtract multiplies two signed 32-bit values, subtracts the result from a
        32-bit accumulate value that is shifted left by 32 bits, and extracts the most significant 32 bits of the result of that
        subtraction.        
        """
        props = {}
        
        name = "SMMLS"
        ins_id = ARMInstruction.smmls
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smmul(self, opcode, encoding):
        """
        A8.8.186
        SMMUL
        Signed Most Significant Word Multiply multiplies two signed 32-bit values, extracts the most significant 32 bits of
        the result, and writes those bits to the destination register.        
        """
        props = {}
        
        name = "SMMUL"
        ins_id = ARMInstruction.smmul
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smuad(self, opcode, encoding):
        """
        A8.8.187
        SMUAD
        Signed Dual Multiply Add performs two signed 16 x 16-bit multiplications. It adds the products together, and writes
        the result to the destination register.        
        """
        props = {}
        
        name = "SMUAD"
        ins_id = ARMInstruction.smuad
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_smusd(self, opcode, encoding):
        """
        A8.8.191
        SMUSD
        Signed Multiply Subtract Dual performs two signed 16 x 16-bit multiplications. It subtracts one of the products from
        the other, and writes the result to the destination register.        
        """
        props = {}
        
        name = "SMUSD"
        ins_id = ARMInstruction.smusd
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ssat(self, opcode, encoding):
        """
        A8.8.193
        SSAT
        Signed Saturate saturates an optionally-shifted signed value to a selectable signed range.        
        """
        props = {}
        
        name = "SSAT"
        ins_id = ARMInstruction.ssat
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(10), 1, I1, 4, I1, 3, 4, 2, I1, 5]
            sh, Rn, imm3, Rd, imm2, sat_imm = decode_opcode(opcode, decode_mask)
            if sh == 1 and ((imm3 << 2) | imm2) == 0:
                return self.decode_ssat16(opcode, encoding)

            saturate_to = sat_imm
            shift_t, shift_n = DecodeImmShift(sh << 1, (imm3 << 2) | imm2)

            if BadReg(Rd) or BadReg(Rn):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Immediate(saturate_to), Register(Rn), RegisterShift(shift_t, shift_n)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I7, 5, 4, 5, 1, I2, 4]
            cond, sat_imm, Rd, imm5, sh, Rn = decode_opcode(opcode, decode_mask)
            saturate_to = sat_imm
            shift_t, shift_n = DecodeImmShift(sh << 1, imm5)
            if Rd == 15 or Rn == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Immediate(saturate_to), Register(Rn), RegisterShift(shift_t, shift_n)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ssat16(self, opcode, encoding):
        """
        A8.8.194
        SSAT16
        Signed Saturate 16 saturates two signed 16-bit values to a selected signed range.        
        """
        props = {}
        
        name = "SSAT16"
        ins_id = ARMInstruction.ssat16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ssax(self, opcode, encoding):
        """
        A8.8.195
        SSAX
        Signed Subtract and Add with Exchange exchanges the two halfwords of the second operand, performs one 16-bit
        integer subtraction and one 16-bit addition, and writes the results to the destination register. It sets the APSR.GE
        bits according to the results.        
        """
        props = {}
        
        name = "SSAX"
        ins_id = ARMInstruction.ssax
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ssub16(self, opcode, encoding):
        """
        A8.8.196
        SSUB16
        Signed Subtract 16 performs two 16-bit signed integer subtractions, and writes the results to the destination register.
        It sets the APSR.GE bits according to the results of the subtractions.        
        """
        props = {}
        
        name = "SSUB16"
        ins_id = ARMInstruction.ssub16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_ssub8(self, opcode, encoding):
        """
        A8.8.197
        SSUB8
        Signed Subtract 8 performs four 8-bit signed integer subtractions, and writes the results to the destination register.
        It sets the APSR.GE bits according to the results of the subtractions.        
        """
        props = {}
        
        name = "SSUB8"
        ins_id = ARMInstruction.ssub8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_stc(self, opcode, encoding):
        """
        A8.8.198
        STC, STC2
        Store Coprocessor stores data from a coprocessor to a sequence of consecutive memory addresses. If no coprocessor
        can execute the instruction, an Undefined Instruction exception is generated.        
        """
        props = {}
        
        name = "STC"
        ins_id = ARMInstruction.stc
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I7, 1, 1, 1, 1, I1, 4, 4, 4, 8]
            P, U, D, W, Rn, CRd, coproc, imm8 = decode_opcode(opcode, decode_mask)
            if P == 0 and U == 0 and D == 0 and W == 0:
                raise UndefinedOpcode()

            if P == 0 and U == 0 and D == 1 and W == 0:
                return self.decode_mcrr(opcode, encoding)

            if coproc in [0b1010, 0b1011]:
                raise RuntimeError("SEE Advanced SIMD and Floating-point")

            cp = coproc
            imm32 = imm8 << 2
            index = P == 1
            add = U == 1
            wback = W == 1

            # if n == 15 && (wback || CurrentInstrSet() != InstrSet_ARM) then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingT2:
            decode_mask = [I7, 1, 1, 1, 1, I1, 4, 4, 4, 8]
            P, U, D, W, Rn, CRd, coproc, imm8 = decode_opcode(opcode, decode_mask)

            if P == 0 and U == 0 and D == 0 and W == 0:
                raise UndefinedOpcode()

            if P == 0 and U == 0 and D == 1 and W == 0:
                return self.decode_mcrr(opcode, encoding)

            if coproc in [0b1010, 0b1011]:
                raise UndefinedOpcode()

            cp = coproc
            imm32 = imm8 << 2
            index = P == 1
            add = U == 1
            wback = W == 1

            # if n == 15 && (wback || CurrentInstrSet() != InstrSet_ARM) then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I3, 1, 1, 1, 1, I1, 4, 4, 4, 8]
            cond, P, U, D, W, Rn, CRd, coproc, imm8 = decode_opcode(opcode, decode_mask)

            if P == 0 and U == 0 and D == 0 and W == 0:
                raise UndefinedOpcode()

            if P == 0 and U == 0 and D == 1 and W == 0:
                return self.decode_mcrr(opcode, encoding)

            if coproc in [0b1010, 0b1011]:
                raise RuntimeError("SEE Advanced SIMD and Floating-point")

            cp = coproc
            imm32 = imm8 << 2
            index = P == 1
            add = U == 1
            wback = W == 1

            # if n == 15 && (wback || CurrentInstrSet() != InstrSet_ARM) then UNPREDICTABLE;
            if Rn == 15 and wback:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA2:
            decode_mask = [I7, 1, 1, 1, 1, I1, 4, 4, 4, 8]
            P, U, D, W, Rn, CRd, coproc, imm8 = decode_opcode(opcode, decode_mask)

            if P == 0 and U == 0 and D == 0 and W == 0:
                raise UndefinedOpcode()

            if P == 0 and U == 0 and D == 1 and W == 0:
                return self.decode_mcrr(opcode, encoding)

            if coproc in [0b1010, 0b1011]:
                raise UndefinedOpcode()

            cp = coproc
            imm32 = imm8 << 2
            index = P == 1
            add = U == 1
            wback = W == 1

            # if n == 15 && (wback || CurrentInstrSet() != InstrSet_ARM) then UNPREDICTABLE;
            if Rn == 15 and wback:
                raise UnpredictableInstructionException()
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if not add:
            imm32 *= -1

        if P == 1 and W == 0:
            operands = [CoprocessorName(coproc), CoprocessorRegister(CRd), Memory(Register(Rn), Immediate(imm32))]

        elif P == 1 and W == 1:
            operands = [CoprocessorName(coproc), CoprocessorRegister(CRd), Memory(Register(Rn), Immediate(imm32), wback=True)]

        elif P == 0 and W == 1:
            operands = [CoprocessorName(coproc), CoprocessorRegister(CRd), Memory(Register(Rn)), Immediate(imm32)]

        elif P == 0 and W == 0 and U == 1:
            operands = [CoprocessorName(coproc), CoprocessorRegister(CRd), Memory(Register(Rn)), Immediate(imm8)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_strd_immediate(self, opcode, encoding):
        """
        A8.8.210
        STRD (immediate)
        Store Register Dual (immediate) calculates an address from a base register value and an immediate offset, and stores
        two words from two registers to memory. It can use offset, post-indexed, or pre-indexed addressing.         
        """
        props = {}
        
        name = "STRD"
        ins_id = ARMInstruction.strd_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []
            
        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_strd_register(self, opcode, encoding):
        """
        A8.8.211
        STRD (register)
        Store Register Dual (register) calculates an address from a base register value and a register offset, and stores two
        words from two registers to memory. It can use offset, post-indexed, or pre-indexed addressing.        
        """
        props = {}
        
        name = "STRD"
        ins_id = ARMInstruction.strd_register
        setsflags = False
        condition = None

        if encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_strh_immediate_thumb(self, opcode, encoding):
        """
        A8.8.216
        STRH (immediate, Thumb)
        Store Register Halfword (immediate) calculates an address from a base register value and an immediate offset, and
        stores a halfword from a register to memory. It can use offset, post-indexed, or pre-indexed addressing                
        """
        props = {}
        
        name = "STRH"
        ins_id = ARMInstruction.strh_immediate_thumb
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT3:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins


    def decode_strh_register(self, opcode, encoding):
        """
        A8.8.218
        STRH (register)
        Store Register Halfword (register) calculates an address from a base register value and an offset register value, and
        stores a halfword from a register to memory. The offset register value can be shifted left by 0, 1, 2, or 3 bits.         
        """
        props = {}
        
        name = "STRH"
        ins_id = ARMInstruction.strh_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_strht(self, opcode, encoding):
        """
        A8.8.219
        STRHT
        Store Register Halfword Unprivileged stores a halfword from a register to memory.
        """
        props = {}
        
        name = "STRHT"
        ins_id = ARMInstruction.strht
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sxtab(self, opcode, encoding):
        """
        A8.8.230
        SXTAB
        Signed Extend and Add Byte extracts an 8-bit value from a register, sign-extends it to 32 bits, adds the result to the
        value in another register, and writes the final result to the destination register. The instruction can specify a rotation
        by 0, 8, 16, or 24 bits before extracting the 8-bit value.        
        """
        props = {}
        
        name = "SXTAB"
        ins_id = ARMInstruction.sxtab
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I4, 4, I2, 2, 4]
            Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            
            if Rn == 0b1111:
                return self.decode_sxtb(opcode, encoding)
            
            rotation = rotate << 3
            
            if BadReg(Rd) or Rn == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I8, 4, 4, 2, I6, 4]
            cond, Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            if Rn == 0b1111:
                return self.decode_sxtb(opcode, encoding)

            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sxtab16(self, opcode, encoding):
        """
        A8.8.231
        SXTAB16
        Signed Extend and Add Byte 16 extracts two 8-bit values from a register, sign-extends them to 16 bits each, adds
        the results to two 16-bit values from another register, and writes the final results to the destination register. The
        instruction can specify a rotation by 0, 8, 16, or 24 bits before extracting the 8-bit values.        
        """
        props = {}
        
        name = "SXTAB16"
        ins_id = ARMInstruction.sxtab16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I4, 4, I2, 2, 4]
            Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            
            if Rn == 0b1111:
                return self.decode_sxtb16(opcode, encoding)
            
            rotation = rotate << 3
            
            if BadReg(Rd) or Rn == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I8, 4, 4, 2, I6, 4]
            cond, Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            if Rn == 0b1111:
                return self.decode_sxtb16(opcode, encoding)

            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sxtah(self, opcode, encoding):
        """
        A8.8.232
        SXTAH
        Signed Extend and Add Halfword extracts a 16-bit value from a register, sign-extends it to 32 bits, adds the result
        to a value from another register, and writes the final result to the destination register. The instruction can specify a
        rotation by 0, 8, 16, or 24 bits before extracting the 16-bit value.        
        """
        props = {}
        
        name = "SXTAH"
        ins_id = ARMInstruction.sxtah
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I4, 4, I2, 2, 4]
            Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            
            if Rn == 0b1111:
                return self.decode_sxth(opcode, encoding)
            
            rotation = rotate << 3
            
            if BadReg(Rd) or Rn == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I8, 4, 4, 2, I6, 4]
            cond, Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            if Rn == 0b1111:
                return self.decode_sxth(opcode, encoding)

            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sxtb(self, opcode, encoding):
        """
        A8.8.233
        SXTB
        Signed Extend Byte extracts an 8-bit value from a register, sign-extends it to 32 bits, and writes the result to the
        destination register. The instruction can specify a rotation by 0, 8, 16, or 24 bits before extracting the 8-bit value.        
        """
        props = {}
        
        name = "SXTB"
        ins_id = ARMInstruction.sxtb
        setsflags = False
        condition = None

        qualifiers = ""
        if encoding == eEncodingT1:
            decode_mask = [I(26), 3, 3]
            Rm, Rd = decode_opcode(opcode, decode_mask)
            rotation = 0
            operands = [Register(Rd), Register(Rm)]

        elif encoding == eEncodingT2:
            decode_mask = [I(20), 4, I2, 2, 4]
            Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            rotation = rotate << 3
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()

            qualifiers = ".W"
            operands = [Register(Rd), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I(12), 4, 2, I6, 4]
            cond, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            rotation = rotate << 3
            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifiers)
        return ins

    def decode_sxtb16(self, opcode, encoding):
        """
        A8.8.234
        SXTB16
        Signed Extend Byte 16 extracts two 8-bit values from a register, sign-extends them to 16 bits each, and writes the
        results to the destination register. The instruction can specify a rotation by 0, 8, 16, or 24 bits before extracting the
        8-bit values.        
        """
        props = {}
        
        name = "SXTB16"
        ins_id = ARMInstruction.sxtb16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_sxth(self, opcode, encoding):
        """
        A8.8.235
        SXTH
        Signed Extend Halfword extracts a 16-bit value from a register, sign-extends it to 32 bits, and writes the result to
        the destination register. The instruction can specify a rotation by 0, 8, 16, or 24 bits before extracting the 16-bit
        value.        
        """
        props = {}
        
        name = "SXTH"
        ins_id = ARMInstruction.sxth
        setsflags = False
        condition = None
        qualifier = ""

        if encoding == eEncodingT1:
            decode_mask = [I(26), 3, 3]
            rotation = 0
            Rm, Rd = decode_opcode(opcode, decode_mask)
            operands = [Register(Rd), Register(Rm)]

        elif encoding == eEncodingT2:
            decode_mask = [I(20), 4, I2, 2, 4]
            Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            rotation = rotate << 3
            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()

            qualifier = ".W"
            operands = [Register(Rd), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I(12), 4, 2, I6, 4]
            cond, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            rotation = rotate << 3
            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rm), RegisterShift(SRType_ROR,rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_uadd16(self, opcode, encoding):
        """
        A8.8.243
        UADD16
        Unsigned Add 16 performs two 16-bit unsigned integer additions, and writes the results to the destination register.
        It sets the APSR.GE bits according to the results of the additions.        
        """
        props = {}
        
        name = "UADD16"
        ins_id = ARMInstruction.uadd16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uadd8(self, opcode, encoding):
        """
        A8.8.244
        UADD8
        Unsigned Add 8 performs four unsigned 8-bit integer additions, and writes the results to the destination register. It
        sets the APSR.GE bits according to the results of the additions.        
        """
        props = {}
        
        name = "UADD8"
        ins_id = ARMInstruction.uadd8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uasx(self, opcode, encoding):
        """
        A8.8.245
        UASX
        Unsigned Add and Subtract with Exchange exchanges the two halfwords of the second operand, performs one
        unsigned 16-bit integer addition and one unsigned 16-bit subtraction, and writes the results to the destination
        register. It sets the APSR.GE bits according to the results        
        """
        props = {}
        
        name = "UASX"
        ins_id = ARMInstruction.uasx
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_udf(self, opcode, encoding):
        """
        A8.8.247
        UDF
        Permanently Undefined generates an Undefined Instruction exception.        
        """
        props = {}
        
        name = "UDF"
        ins_id = ARMInstruction.udf
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_udiv(self, opcode, encoding):
        """
        A8.8.248
        UDIV
        Unsigned Divide divides a 32-bit unsigned integer register value by a 32-bit unsigned integer register value, and
        writes the result to the destination register. The condition flags are not affected.                
        """
        props = {}
        
        name = "UDIV"
        ins_id = ARMInstruction.udiv
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uhadd16(self, opcode, encoding):
        """
        A8.8.249
        UHADD16
        Unsigned Halving Add 16 performs two unsigned 16-bit integer additions, halves the results, and writes the results
        to the destination register.        
        """
        props = {}
        
        name = "UHADD16"
        ins_id = ARMInstruction.uhadd16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uhadd8(self, opcode, encoding):
        """
        A8.8.250
        UHADD8
        Unsigned Halving Add 8 performs four unsigned 8-bit integer additions, halves the results, and writes the results to
        the destination register        
        """
        props = {}
        
        name = "UHADD8"
        ins_id = ARMInstruction.uhadd8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uhasx(self, opcode, encoding):
        """
        A8.8.251
        UHASX
        Unsigned Halving Add and Subtract with Exchange exchanges the two halfwords of the second operand, performs
        one unsigned 16-bit integer addition and one unsigned 16-bit subtraction, halves the results, and writes the results
        to the destination register.        
        """
        props = {}
        
        name = "UHASX"
        ins_id = ARMInstruction.uhasx
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uhsax(self, opcode, encoding):
        """
        A8.8.252
        UHSAX
        Unsigned Halving Subtract and Add with Exchange exchanges the two halfwords of the second operand, performs
        one unsigned 16-bit integer subtraction and one unsigned 16-bit addition, halves the results, and writes the results
        to the destination register.        
        """
        props = {}
        
        name = "UHSAX"
        ins_id = ARMInstruction.uhsax
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uhsub16(self, opcode, encoding):
        """
        A8.8.253
        UHSUB16
        Unsigned Halving Subtract 16 performs two unsigned 16-bit integer subtractions, halves the results, and writes the
        results to the destination register                
        """
        props = {}
        
        name = "UHSUB16"
        ins_id = ARMInstruction.uhsub16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uhsub8(self, opcode, encoding):
        """
        A8.8.254
        UHSUB8
        Unsigned Halving Subtract 8 performs four unsigned 8-bit integer subtractions, halves the results, and writes the
        results to the destination register.        
        """
        props = {}
        
        name = "UHSUB8"
        ins_id = ARMInstruction.uhsub8
        setsflags = False
        condition = None
        
        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uqadd16(self, opcode, encoding):
        """
        A8.8.258
        UQADD16
        Unsigned Saturating Add 16 performs two unsigned 16-bit integer additions, saturates the results to the 16-bit
        unsigned integer range 0 x 216 - 1, and writes the results to the destination register.
        """
        props = {}
        
        name = "UQADD16"
        ins_id = ARMInstruction.uqadd16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uqadd8(self, opcode, encoding):
        """
        A8.8.259
        UQADD8
        Unsigned Saturating Add 8 performs four unsigned 8-bit integer additions, saturates the results to the 8-bit unsigned
        integer range 0 x 28 - 1, and writes the results to the destination register.        
        """
        props = {}
        
        name = "UQADD8"
        ins_id = ARMInstruction.uqadd8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uqasx(self, opcode, encoding):
        """
        A8.8.260
        UQASX
        Unsigned Saturating Add and Subtract with Exchange exchanges the two halfwords of the second operand,
        performs one unsigned 16-bit integer addition and one unsigned 16-bit subtraction, saturates the results to the 16-bit
        unsigned integer range 0 x 216 - 1, and writes the results to the destination register.        
        """
        props = {}
        
        name = "UQASX"
        ins_id = ARMInstruction.uqasx
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uqsax(self, opcode, encoding):
        """
        A8.8.261
        UQSAX
        Unsigned Saturating Subtract and Add with Exchange exchanges the two halfwords of the second operand,
        performs one unsigned 16-bit integer subtraction and one unsigned 16-bit addition, saturates the results to the 16-bit
        unsigned integer range 0 x 216 - 1, and writes the results to the destination register.
        """
        props = {}
        
        name = "UQSAX"
        ins_id = ARMInstruction.uqsax
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uqsub16(self, opcode, encoding):
        """
        A8.8.262
        UQSUB16
        Unsigned Saturating Subtract 16 performs two unsigned 16-bit integer subtractions, saturates the results to the
        16-bit unsigned integer range 0 x 216 - 1, and writes the results to the destination register.        
        """
        props = {}
        
        name = "UQSUB16"
        ins_id = ARMInstruction.uqsub16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uqsub8(self, opcode, encoding):
        """
        A8.8.263
        UQSUB8
        Unsigned Saturating Subtract 8 performs four unsigned 8-bit integer subtractions, saturates the results to the 8-bit
        unsigned integer range 0 x 28 - 1, and writes the results to the destination register.        
        """
        props = {}
        
        name = "UQSUB8"
        ins_id = ARMInstruction.uqsub8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_usad8(self, opcode, encoding):
        """
        A8.8.264
        USAD8
        Unsigned Sum of Absolute Differences performs four unsigned 8-bit subtractions, and adds the absolute values of
        the differences together.        
        """
        props = {}
        
        name = "USAD8"
        ins_id = ARMInstruction.usad8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_usada8(self, opcode, encoding):
        """
        A8.8.265
        USADA8
        Unsigned Sum of Absolute Differences and Accumulate performs four unsigned 8-bit subtractions, and adds the
        absolute values of the differences to a 32-bit accumulate operand.        
        """
        props = {}
        
        name = "USADA8"
        ins_id = ARMInstruction.usada8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_usat(self, opcode, encoding):
        """
        A8.8.266
        USAT
        Unsigned Saturate saturates an optionally-shifted signed value to a selected unsigned range.        
        """
        props = {}
        
        name = "USAT"
        ins_id = ARMInstruction.usat
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_usat16(self, opcode, encoding):
        """
        A8.8.267
        USAT16
        Unsigned Saturate 16 saturates two signed 16-bit values to a selected unsigned range.        
        """
        props = {}
        
        name = "USAT16"
        ins_id = ARMInstruction.usat16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_usax(self, opcode, encoding):
        """
        A8.8.268
        USAX
        Unsigned Subtract and Add with Exchange exchanges the two halfwords of the second operand, performs one
        unsigned 16-bit integer subtraction and one unsigned 16-bit addition, and writes the results to the destination
        register. It sets the APSR.GE bits according to the results.        
        """
        props = {}
        
        name = "USAX"
        ins_id = ARMInstruction.usax
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_usub16(self, opcode, encoding):
        """
        A8.8.269
        USUB16
        Unsigned Subtract 16 performs two 16-bit unsigned integer subtractions, and writes the results to the destination
        register. It sets the APSR.GE bits according to the results of the subtractions.        
        """
        props = {}
        
        name = "USUB16"
        ins_id = ARMInstruction.usub16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_usub8(self, opcode, encoding):
        """
        A8.8.270
        USUB8
        Unsigned Subtract 8 performs four 8-bit unsigned integer subtractions, and writes the results to the destination
        register. It sets the APSR.GE bits according to the results of the subtractions.        
        """
        props = {}
        
        name = "USUB8"
        ins_id = ARMInstruction.usub8
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uxtab(self, opcode, encoding):
        """
        A8.8.271
        UXTAB
        Unsigned Extend and Add Byte extracts an 8-bit value from a register, zero-extends it to 32 bits, adds the result to
        the value in another register, and writes the final result to the destination register. The instruction can specify a
        rotation by 0, 8, 16, or 24 bits before extracting the 8-bit value.        
        """
        props = {}
        
        name = "UXTAB"
        ins_id = ARMInstruction.uxtab
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I4, 4, I2, 2, 4]
            Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            if Rn == 0b1111:
                return self.decode_uxtb(opcode, eEncodingT2)

            rotation = rotate << 3
            if BadReg(Rd) or Rn == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I8, 4, 4, 2, I6, 4]
            cond, Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            if Rn == 0b1111:
                return self.decode_uxtb(opcode, encoding)

            rotation = rotate << 3
            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uxtab16(self, opcode, encoding):
        """
        A8.8.272
        UXTAB16
        Unsigned Extend and Add Byte 16 extracts two 8-bit values from a register, zero-extends them to 16 bits each, adds
        the results to two 16-bit values from another register, and writes the final results to the destination register. The
        instruction can specify a rotation by 0, 8, 16, or 24 bits before extracting the 8-bit values.        
        """
        props = {}
        
        name = "UXTAB16"
        ins_id = ARMInstruction.uxtab16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I4, 4, I2, 2, 4]
            Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            if Rn == 0b1111:
                return self.decode_uxtb16(opcode, encoding)

            rotation = rotate << 3
            if BadReg(Rd) or Rn == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I8, 4, 4, 2, I6, 4]
            cond, Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            if Rn == 0b1111:
                return self.decode_uxtb16(opcode, encoding)

            rotation = rotate << 3
            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uxtah(self, opcode, encoding):
        """
        A8.8.273
        UXTAH
        Unsigned Extend and Add Halfword extracts a 16-bit value from a register, zero-extends it to 32 bits, adds the result
        to a value from another register, and writes the final result to the destination register. The instruction can specify a
        rotation by 0, 8, 16, or 24 bits before extracting the 16-bit value.        
        """
        props = {}
        
        name = "UXTAH"
        ins_id = ARMInstruction.uxtah
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(12), 4, I4, 4, I2, 2, 4]
            Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            if Rn == 0b1111:
                return self.decode_uxtb(opcode, encoding)

            rotation = rotate << 3
            if BadReg(Rd) or Rn == 13 or BadReg(Rm):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        elif encoding == eEncodingA1:
            decode_mask = [4, I8, 4, 4, 2, I6, 4]
            cond, Rn, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            if Rn == 0b1111:
                return self.decode_uxtb(opcode, encoding)

            rotation = rotate << 3
            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uxtb16(self, opcode, encoding):
        """
        A8.8.275
        UXTB16
        Unsigned Extend Byte 16 extracts two 8-bit values from a register, zero-extends them to 16 bits each, and writes
        the results to the destination register. The instruction can specify a rotation by 0, 8, 16, or 24 bits before extracting
        the 8-bit values.        
        """
        props = {}
        
        name = "UXTB16"
        ins_id = ARMInstruction.uxtb16
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_uxth(self, opcode, encoding):
        """
        A8.8.276
        UXTH
        Unsigned Extend Halfword extracts a 16-bit value from a register, zero-extends it to 32 bits, and writes the result to
        the destination register. The instruction can specify a rotation by 0, 8, 16, or 24 bits before extracting the 16-bit
        value.        
        """
        props = {}
        
        name = "UXTH"
        ins_id = ARMInstruction.uxth
        setsflags = False
        condition = None

        qualifier = ""
        if encoding == eEncodingT1:
            decode_mask = [I(26), 3, 3]
            Rm, Rd = decode_opcode(opcode, decode_mask)
            rotation = 0
            operands = [Register(Rd), Register(Rm)]

        elif encoding == eEncodingT2:
            decode_mask = [I(20), 4, I2, 2, 4]
            Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            rotation = rotate << 3

            if BadReg(Rd) or BadReg(Rm):
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rm), RegisterShift(SRType_ROR, rotation)]
            qualifier = ".W"

        elif encoding == eEncodingA1:
            decode_mask = [4, I(12), 4, 2, I6, 4]
            cond, Rd, rotate, Rm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            rotation = rotate << 3            

            if Rd == 15 or Rm == 15:
                raise UnpredictableInstructionException()

            operands = [Register(Rd), Register(Rm), RegisterShift(SRType_ROR, rotation)]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vaba(self, opcode, encoding):
        """
        A8.8.277
        VABA, VABAL
        Vector Absolute Difference and Accumulate {Long} subtracts the elements of one vector from the corresponding
        elements of another vector, and accumulates the absolute values of the results into the elements of the destination
        vector.        
        """
        props = {}
        
        name = "VABA"
        ins_id = ARMInstruction.vaba
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vabd_int(self, opcode, encoding):
        """
        A8.8.278
        VABD, VABDL (integer)
        Vector Absolute Difference {Long} (integer) subtracts the elements of one vector from the corresponding elements
        of another vector, and places the absolute values of the results in the elements of the destination vector.        
        """
        props = {}
        
        name = "VABD"
        ins_id = ARMInstruction.vabd_int
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vabd_fp(self, opcode, encoding):
        """
        A8.8.279
        VABD (floating-point)
        Vector Absolute Difference (floating-point) subtracts the elements of one vector from the corresponding elements
        of another vector, and places the absolute values of the results in the elements of the destination vector.        
        """
        props = {}
        
        name = "VABD"
        ins_id = ARMInstruction.vabd_fp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vabs(self, opcode, encoding):
        """
        A8.8.280
        VABS
        Vector Absolute takes the absolute value of each element in a vector, and places the results in a second vector. The
        floating-point version only clears the sign bit.        
        """
        props = {}
        
        name = "VABS"
        ins_id = ARMInstruction.vabs
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vac(self, opcode, encoding):
        """
        A8.8.281
        VACGE, VACGT, VACLE, VACLT
        VACGE (Vector Absolute Compare Greater Than or Equal) and VACGT (Vector Absolute Compare Greater Than) take
        the absolute value of each element in a vector, and compare it with the absolute value of the corresponding element
        of a second vector. If the condition is true, the corresponding element in the destination vector is set to all ones.
        Otherwise, it is set to all zeros.        
        """
        props = {}
        
        name = "VACGE"
        ins_id = ARMInstruction.vac
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vadd_int(self, opcode, encoding):
        """
        A8.8.282
        VADD (integer)
        Vector Add adds corresponding elements in two vectors, and places the results in the destination vector.        
        """
        props = {}
        
        name = "VADD"
        ins_id = ARMInstruction.vadd_int
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vadd_fp(self, opcode, encoding):
        """
        A8.8.283
        VADD (floating-point)
        Vector Add adds corresponding elements in two vectors, and places the results in the destination vecto        
        """
        props = {}
        
        name = "VADD"
        ins_id = ARMInstruction.vadd_fp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vaddhn(self, opcode, encoding):
        """
        A8.8.284
        VADDHN
        Vector Add and Narrow, returning High Half adds corresponding elements in two quadword vectors, and places the
        most significant half of each result in a doubleword vector. The results are truncated.         
        """
        props = {}
        
        name = "VADDHN"
        ins_id = ARMInstruction.vaddhn
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vadd(self, opcode, encoding):
        """
        A8.8.285
        VADDL, VADDW
        VADDL (Vector Add Long) adds corresponding elements in two doubleword vectors, and places the results in a
        quadword vector. Before adding, it sign-extends or zero-extends the elements of both operands.        
        """
        props = {}
        
        name = "VADD"
        ins_id = ARMInstruction.vadd
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vand_register(self, opcode, encoding):
        """
        A8.8.287
        VAND (register)
        This instruction performs a bitwise AND operation between two registers, and places the result in the destination
        register.        
        """
        props = {}
        
        name = "VAND"
        ins_id = ARMInstruction.vand_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 1, I2, 4, 4, I4, 1, 1, 1, I1, 4]
            D, Vn, Vd, N, Q, M, Vm = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I9, 1, I2, 4, 4, I4, 1, 1, 1, I1, 4]
            D, Vn, Vd, N, Q, M, Vm = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        # if Q == '1' && (Vd<0> == '1' || Vn<0> == '1' || Vm<0> == '1') then UNDEFINED;
        # d = UInt(D:Vd); n = UInt(N:Vn); m = UInt(M:Vm); regs = if Q == '0' then 1 else 2;
        if Q == 1 and (get_bit(Vd, 0) == 1 or get_bit(Vn, 0) == 1 or get_bit(Vm, 0) == 1):
            raise UndefinedOpcode()

        d = (D << 4) | Vd
        n = (N << 4) | Vn
        m = (M << 4) | Vm
        regs = 1 if Q == 0 else 2

        if Q == 1:
            qualifier = ".64"
            if regs == 1:
                operands = [QRegister(n), QRegister(m)]
            else:
                operands = [QRegister(d), QRegister(n), QRegister(m)]
        else:
            qualifier = ".32"
            if regs == 1:
                operands = [DRegister(n), DRegister(m)]
            else:
                operands = [DRegister(d), DRegister(n), DRegister(m)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vbic_immediate(self, opcode, encoding):
        """
        A8.8.288
        VBIC (immediate)
        Vector Bitwise Bit Clear (immediate) performs a bitwise AND between a register value and the complement of an
        immediate value, and returns the result into the destination vector.         
        """
        props = {}
        
        name = "VBIC"
        ins_id = ARMInstruction.vbic_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vbic_register(self, opcode, encoding):
        """
        A8.8.289
        VBIC (register)
        Vector Bitwise Bit Clear (register) performs a bitwise AND between a register value and the complement of a
        register value, and places the result in the destination register.        
        """
        props = {}
        
        name = "VBIC"
        ins_id = ARMInstruction.vbic_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vb(self, opcode, encoding):
        """
        A8.8.290
        VBIF, VBIT, VBSL
        VBIF (Vector Bitwise Insert if False), VBIT (Vector Bitwise Insert if True), and VBSL (Vector Bitwise Select) perform
        bitwise selection under the control of a mask, and place the results in the destination register. The registers can be
        either quadword or doubleword, and must all be the same size.        
        """
        props = {}
        
        name = "VB"
        ins_id = ARMInstruction.vb
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vceq_register(self, opcode, encoding):
        """
        A8.8.291
        VCEQ (register)
        VCEQ (Vector Compare Equal) takes each element in a vector, and compares it with the corresponding element of a
        second vector. If they are equal, the corresponding element in the destination vector is set to all ones. Otherwise, it
        is set to all zeros        
        """
        props = {}
        
        name = "VCEQ"
        ins_id = ARMInstruction.vceq_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vceq_immediate(self, opcode, encoding):
        """
        A8.8.292
        VCEQ (immediate #0)
        VCEQ #0 (Vector Compare Equal to zero) takes each element in a vector, and compares it with zero. If it is equal to
        zero, the corresponding element in the destination vector is set to all ones. Otherwise, it is set to all zeros.        
        """
        props = {}
        
        name = "VCEQ"
        ins_id = ARMInstruction.vceq_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcge_register(self, opcode, encoding):
        """
        A8.8.293
        VCGE (register)
        VCGE (Vector Compare Greater Than or Equal) takes each element in a vector, and compares it with the
        corresponding element of a second vector. If the first is greater than or equal to the second, the corresponding
        element in the destination vector is set to all ones. Otherwise, it is set to all zeros.        
        """
        props = {}
        
        name = "VCGE"
        ins_id = ARMInstruction.vcge_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcge_immediate(self, opcode, encoding):
        """
        A8.8.294
        VCGE (immediate #0)
        VCGE #0 (Vector Compare Greater Than or Equal to Zero) take each element in a vector, and compares it with zero.
        If it is greater than or equal to zero, the corresponding element in the destination vector is set to all ones. Otherwise,
        it is set to all zeros.        
        """
        props = {}
        
        name = "VCGE"
        ins_id = ARMInstruction.vcge_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcgt_register(self, opcode, encoding):
        """
        A8.8.295
        VCGT (register)
        VCGT (Vector Compare Greater Than) takes each element in a vector, and compares it with the corresponding element
        of a second vector. If the first is greater than the second, the corresponding element in the destination vector is set
        to all ones. Otherwise, it is set to all zeros.        
        """
        props = {}
        
        name = "VCGT"
        ins_id = ARMInstruction.vcgt_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcgt_immediate(self, opcode, encoding):
        """
        A8.8.296
        VCGT (immediate #0)
        VCGT #0 (Vector Compare Greater Than Zero) take each element in a vector, and compares it with zero. If it is greater
        than zero, the corresponding element in the destination vector is set to all ones. Otherwise, it is set to all zeros.        
        """
        props = {}
        
        name = "VCGT"
        ins_id = ARMInstruction.vcgt_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcle_immediate(self, opcode, encoding):
        """
        A8.8.298
        VCLE (immediate #0)
        VCLE #0 (Vector Compare Less Than or Equal to Zero) take each element in a vector, and compares it with zero. If
        it is less than or equal to zero, the corresponding element in the destination vector is set to all ones. Otherwise, it is
        set to all zeros.        
        """
        props = {}
        
        name = "VCLE"
        ins_id = ARMInstruction.vcle_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcls(self, opcode, encoding):
        """
        A8.8.299
        VCLS
        Vector Count Leading Sign Bits counts the number of consecutive bits following the topmost bit, that are the same
        as the topmost bit, in each element in a vector, and places the results in a second vector. The count does not include
        the topmost bit itself.        
        """
        props = {}
        
        name = "VCLS"
        ins_id = ARMInstruction.vcls
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vclt_immediate(self, opcode, encoding):
        """
        A8.8.301
        VCLT (immediate #0)
        VCLT #0 (Vector Compare Less Than Zero) take each element in a vector, and compares it with zero. If it is less than
        zero, the corresponding element in the destination vector is set to all ones. Otherwise, it is set to all zeros.        
        """
        props = {}
        
        name = "VCLT"
        ins_id = ARMInstruction.vclt_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vclz(self, opcode, encoding):
        """
        A8.8.302
        VCLZ
        Vector Count Leading Zeros counts the number of consecutive zeros, starting from the most significant bit, in each
        element in a vector, and places the results in a second vector.        
        """
        props = {}
        
        name = "VCLZ"
        ins_id = ARMInstruction.vclz
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcmp(self, opcode, encoding):
        """
        A8.8.303
        VCMP, VCMPE
        This instruction compares two floating-point registers, or one floating-point register and zero. It writes the result to
        the FPSCR flags. These are normally transferred to the ARM flags by a subsequent VMRS instruction.        
        """
        props = {}
        
        name = "VCMP"
        ins_id = ARMInstruction.vcmp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcnt(self, opcode, encoding):
        """
        A8.8.304
        VCNT
        This instruction counts the number of bits that are one in each element in a vector, and places the results in a second
        vector.        
        """
        props = {}
        
        name = "VCNT"
        ins_id = ARMInstruction.vcnt
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vcv(self, opcode, encoding):
        """
        A8.8.311
        VCVTB, VCVTT
        """
        props = {}
        
        name = "VCVT"
        ins_id = ARMInstruction.vcv
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 1, I5, 1, 4, I4, 1, I1, 1, I1, 4]
            D, op, Vd, T, M, Vm = decode_opcode(opcode, decode_mask)

        elif encoding == eEncodingA1:
            decode_mask = [4, I5, 1, I5, 1, 4, I4, 1, I1, 1, I1, 4]
            D, op, Vd, T, M, Vm = decode_opcode(opcode, decode_mask)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        # half_to_single = (op == '0');
        half_to_single = op == 0

        # lowbit = if T == '1' then 16 else 0;
        lowbit = 16 if T == 1 else 0

        # m = UInt(Vm:M); d = UInt(Vd:D);
        Sm = (Vm << 1) | M
        Sd = (Vd << 1) | D

        name += "B" if T == 0 else "T"
        name += ".F32.F16" if op == 0 else ".F16.F32"
        
        # TODO: I think these registers are not general purpose.
        operands = [Register(Sd), Register(Sm)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vdiv(self, opcode, encoding):
        """
        A8.8.312
        VDIV
        This instruction divides one floating-point value by another floating-point value and writes the result to a third
        floating-point register.        
        """
        props = {}
        
        name = "VDIV"
        ins_id = ARMInstruction.vdiv
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vdup_scalar(self, opcode, encoding):
        """
        A8.8.313
        VDUP (scalar)
        Vector Duplicate duplicates a scalar into every element of the destination vector.        
        """
        props = {}
        
        name = "VDUP"
        ins_id = ARMInstruction.vdup_scalar
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vdup_arm(self, opcode, encoding):
        """
        A8.8.314
        VDUP (ARM core register)
        This instruction duplicates an element from an ARM core register into every element of the destination vector.        
        """
        props = {}
        
        name = "VDUP"
        ins_id = ARMInstruction.vdup_arm
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_veor(self, opcode, encoding):
        """
        A8.8.315
        VEOR
        Vector Bitwise Exclusive OR performs a bitwise Exclusive OR operation between two registers, and places the
        result in the destination register. The operand and result registers can be quadword or doubleword. They must all be
        the same size.        
        """
        props = {}
        
        name = "VEOR"
        ins_id = ARMInstruction.veor
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 1, I2, 4, 4, I4, 1, 1, 1, I1, 4]
            D, Vn, Vd, N, Q, M, Vm = decode_opcode(opcode, decode_mask)

        elif encoding == eEncodingA1:
            decode_mask = [I9, 1, I2, 4, 4, I4, 1, 1, 1, I1, 4]
            D, Vn, Vd, N, Q, M, Vm = decode_opcode(opcode, decode_mask)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if Q == 1 and (get_bit(Vd, 0) == 1 or get_bit(Vn, 0) == 1 or get_bit(Vm, 0) == 1):
            raise UndefinedOpcode()

        d = (D << 4) | Vd
        n = (N << 4) | Vn
        m = (M << 4) | Vm

        regs = 1 if Q == 0 else 2

        if Q == 1:
            qualifier = ".64"
            if regs == 1:
                operands = [QRegister(n), QRegister(m)]
            else:
                operands = [QRegister(d), QRegister(n), QRegister(m)]
        else:
            qualifier = ".32"
            if regs == 1:
                operands = [DRegister(n), DRegister(m)]
            else:
                operands = [DRegister(d), DRegister(n), DRegister(m)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vext(self, opcode, encoding):
        """
        A8.8.316
        VEXT
        Vector Extract extracts elements from the bottom end of the second operand vector and the top end of the first,
        concatenates them and places the result in the destination vector.         
        """
        props = {}
        
        name = "VEXT"
        ins_id = ARMInstruction.vext
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vfm(self, opcode, encoding):
        """
        A8.8.317
        VFMA, VFMS
        Vector Fused Multiply Accumulate multiplies corresponding elements of two vectors, and accumulates the results
        into the elements of the destination vector. The instruction does not round the result of the multiply before the
        accumulation        
        """
        props = {}
        
        name = "VFMA"
        ins_id = ARMInstruction.vfm
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vfnm(self, opcode, encoding):
        """
        A8.8.318
        VFNMA, VFNMS
        Vector Fused Negate Multiply Accumulate negates one floating-point register value and multiplies it by another
        floating-point register value, adds the negation of the floating-point value in the destination register to the product,
        and writes the result back to the destination register. The instruction does not round the result of the multiply before
        the addition.        
        """
        props = {}
        
        name = "VFNMA"
        ins_id = ARMInstruction.vfnm
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vh(self, opcode, encoding):
        """
        A8.8.319
        VHADD, VHSUB
        Vector Halving Add adds corresponding elements in two vectors of integers, shifts each result right one bit, and
        places the final results in the destination vector. The results of the halving operations are truncated (for rounded
        results see VRHADD on page A8-1028).        
        """
        props = {}
        
        name = "VHADD"
        ins_id = ARMInstruction.vh
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vldm(self, opcode, encoding):
        """
        A8.8.332
        VLDM
        Vector Load Multiple loads multiple extension registers from consecutive memory locations using an address from
        an ARM core register.        
        """
        props = {}
        
        name = "VLDM"
        ins_id = ARMInstruction.vldm
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmax_vmin_int(self, opcode, encoding):
        """
        A8.8.334
        VMAX, VMIN (integer)
        Vector Maximum compares corresponding elements in two vectors, and copies the larger of each pair into the
        corresponding element in the destination vector.        
        """
        props = {}
        
        name = "VMAX"
        ins_id = ARMInstruction.vmax_vmin_int
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmax_vmin_fp(self, opcode, encoding):
        """
        A8.8.335
        VMAX, VMIN (floating-point)
        Vector Maximum compares corresponding elements in two vectors, and copies the larger of each pair into the
        corresponding element in the destination vector.        
        """
        props = {}
        
        name = "VMAX"
        ins_id = ARMInstruction.vmax_vmin_fp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmla_vmlal_vmls_vmlsl_int(self, opcode, encoding):
        """
        A8.8.336
        VMLA, VMLAL, VMLS, VMLSL (integer)
        Vector Multiply Accumulate and Vector Multiply Subtract multiply corresponding elements in two vectors, and
        either add the products to, or subtract them from, the corresponding elements of the destination vector. Vector
        Multiply Accumulate Long and Vector Multiply Subtract Long do the same thing, but with destination vector
        elements that are twice as long as the elements that are multiplied.        
        """
        props = {}
        
        name = "VMLA"
        ins_id = ARMInstruction.vmla_vmlal_vmls_vmlsl_int
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmla_vmls_fp(self, opcode, encoding):
        """
        A8.8.337
        VMLA, VMLS (floating-point)
        Vector Multiply Accumulate multiplies corresponding elements in two vectors, and accumulates the results into the
        elements of the destination vector.        
        """
        props = {}
        
        name = "VMLA"
        ins_id = ARMInstruction.vmla_vmls_fp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmla_vmlal_vmls_vmlsl_by_scalar(self, opcode, encoding):
        """
        A8.8.338
        VMLA, VMLAL, VMLS, VMLSL (by scalar)
        Vector Multiply Accumulate and Vector Multiply Subtract multiply elements of a vector by a scalar, and either add
        the products to, or subtract them from, corresponding elements of the destination vector.         
        """
        props = {}
        
        name = "VMLA"
        ins_id = ARMInstruction.vmla_vmlal_vmls_vmlsl_by_scalar
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmov_immediate(self, opcode, encoding):
        """
        A8.8.339
        VMOV (immediate)
        This instruction places an immediate constant into every element of the destination register.        
        """
        props = {}
        
        name = "VMOV"
        ins_id = ARMInstruction.vmov_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I3, 1, I5, 1, I3, 3, 4, 4, I1, 1, 1, I1, 4]
            i, D, imm3, Vd, cmode, Q, op, imm4 = decode_opcode(opcode, decode_mask)

            # if op == '0' && cmode<0> == '1' && cmode<3:2> != '11' then SEE VORR (immediate);
            if op == 0 and get_bit(cmode, 0) == 1 and get_bits(cmode, 3, 2) != 0b11:
                return self.decode_vorr_immediate(opcode, encoding)

            # if op == '1' && cmode != '1110' then SEE "Related encodings";
            if op == 1 and cmode != 0b1110:
                raise RuntimeError("SEE Related encodings")

            # if Q == '1' && Vd<0> == '1' then UNDEFINED;
            if Q == 1 and get_bit(Vd, 0) == 1:
                raise UndefinedOpcode()

            # i:imm3:imm4
            imm32 = (i << (3 + 4)) | (imm3 << 4) | imm4

            # single_register = FALSE; advsimd = TRUE; imm64 = AdvSIMDExpandImm(op, cmode, i:imm3:imm4);
            single_register = False
            advsimd = True
            immediate = AdvSIMDExpandImm(op, cmode, imm32)

            # d = UInt(D:Vd); regs = if Q == '0' then 1 else 2;
            d = (D << 4) | Vd
            regs = 1 if Q == 0 else 2

        elif encoding == eEncodingT2:
            decode_mask = [I9, 1, I2, 4, 4, I3, 1, I4, 4]
            D, imm4H, Vd, sz, imm4L = decode_opcode(opcode, decode_mask)

            # single_register = (sz == '0'); advsimd = FALSE;
            # if single_register then
            #     d = UInt(Vd:D); imm32 = VFPExpandImm(imm4H:imm4L, 32);
            # else
            #     d = UInt(D:Vd); imm64 = VFPExpandImm(imm4H:imm4L, 64); regs = 1;            
            single_register = sz == 0
            advsimd = False
            imm8 = (imm4H << 4) | imm4L
            if single_register:
                d = (Vd << 1) | D
                immediate = VFPExpandImm(imm8, 32)
            
            else:
                d = (D << 4) | Vd
                immediate = VFPExpandImm(imm8, 64)
                immediate = imm8
                regs = 1

        elif encoding == eEncodingA1:
            decode_mask = [I7, 1, I1, 1, I3, 3, 4, 4, I1, 1, 1, I1, 4]
            i, D, imm3, Vd, cmode, Q, op, imm4 = decode_opcode(opcode, decode_mask)

            # if op == '0' && cmode<0> == '1' && cmode<3:2> != '11' then SEE VORR (immediate);
            if op == 0 and get_bit(cmode, 0) == 1 and get_bits(cmode, 3, 2) != 0b11:
                return self.decode_vorr_immediate(opcode, encoding)

            # if op == '1' && cmode != '1110' then SEE "Related encodings";
            if op == 1 and cmode != 0b1110:
                raise RuntimeError("SEE Related encodings")

            # if Q == '1' && Vd<0> == '1' then UNDEFINED;
            if Q == 1 and get_bit(Vd, 0) == 1:
                raise UndefinedOpcode()

            # i:imm3:imm4
            imm32 = (i << (3 + 4)) | (imm3 << 4) | imm4

            # single_register = FALSE; advsimd = TRUE; imm64 = AdvSIMDExpandImm(op, cmode, i:imm3:imm4);
            single_register = False
            advsimd = True
            immediate = AdvSIMDExpandImm(op, cmode, imm32)

            # d = UInt(D:Vd); regs = if Q == '0' then 1 else 2;
            d = (D << 4) | Vd
            regs = 1 if Q == 0 else 2

        elif encoding == eEncodingA2:
            decode_mask = [4, I5, 1, I2, 4, 4, I3, 1, I4, 4]
            cond, D, imm4H, Vd, sz, imm4L = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            # single_register = (sz == '0'); advsimd = FALSE;
            # if single_register then
            #     d = UInt(Vd:D); imm32 = VFPExpandImm(imm4H:imm4L, 32);
            # else
            #     d = UInt(D:Vd); imm64 = VFPExpandImm(imm4H:imm4L, 64); regs = 1;            
            single_register = sz == 0
            advsimd = False
            imm8 = (imm4H << 4) | imm4L
            if single_register:
                d = (Vd << 1) | D
                immediate = VFPExpandImm(imm8, 32)
            
            else:
                d = (D << 4) | Vd
                immediate = VFPExpandImm(imm8, 64)
                regs = 1

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if encoding in [eEncodingT1, eEncodingA1]:
            if Q == 1:
                # VMOV{<c>}{<q>}.<dt> <Qd>, #<imm> Encoding T1/A1, Q = 1
                qualifier = ".I64"
                operands = [QRegister(d), Immediate(immediate)]
            
            else:
                # VMOV{<c>}{<q>}.<dt> <Dd>, #<imm> Encoding T1/A1, Q = 0
                qualifier = ".I32"
                operands = [DRegister(d), Immediate(immediate)]
        
        else:
            if sz == 1:
                # VMOV{<c>}{<q>}.F64 <Dd>, #<imm> Encoding T2/A2, sz = 1
                qualifier = ".F64"
                operands = [DRegister(d), Immediate(immediate)]
            
            else:
                # VMOV{<c>}{<q>}.F32 <Sd>, #<imm> Encoding T2/A2, sz = 0
                qualifier = ".F32"
                operands = [SRegister(d), Immediate(immediate)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vmov_register(self, opcode, encoding):
        """
        A8.8.340
        VMOV (register)
        This instruction copies the contents of one register to another.        
        """
        props = {}
        
        name = "VMOV"
        ins_id = ARMInstruction.vmov_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 1, I2, 4, 4, I4, 1, 1, 1, I1, 4]
            D, Vm1, Vd, M1, Q, M2, Vm2 = decode_opcode(opcode, decode_mask)
            
            # if !Consistent(M) || !Consistent(Vm) then SEE VORR (register);
            # if Q == '1' && (Vd<0> == '1' || Vm<0> == '1') then UNDEFINED;
            # single_register = FALSE; advsimd = TRUE;
            # d = UInt(D:Vd); m = UInt(M:Vm); regs = if Q == '0' then 1 else 2;
            if M1 != M2 or Vm1 != Vm2:
                return self.decode_vorr_register(opcode, encoding)
            
            if Q == 1 and (get_bit(Vd, 0) == 1 or get_bit(Vm1, 0) == 1):
                raise UndefinedOpcode()
            
            single_register = False
            advsimd = True
            
            d = (D << 4) | Vd
            m = (M1 << 4) | Vm1
            regs = 1 if Q == 0 else 2

        elif encoding == eEncodingT2:
            decode_mask = [I9, 1, I6, 4, I3, 1, I2, 1, I1, 4]
            D, Vd, sz, M, Vm = decode_opcode(opcode, decode_mask)
            operands = []

            # single_register = (sz == '0'); advsimd = FALSE;
            # if single_register then
            #     d = UInt(Vd:D); m = UInt(Vm:M);
            # else
            #     d = UInt(D:Vd); m = UInt(M:Vm); regs = 1;
            single_register = sz == 0
            advsimd = False
            if single_register:
                d = (Vd << 1) | D
                m = (Vm << 1) | M
            else:
                d = (D << 4) | Vd
                m = (M << 4) | Vm
                regs = 1

        elif encoding == eEncodingA1:
            decode_mask = [I9, 1, I2, 4, 4, I4, 1, 1, 1, I1, 4]
            D, Vm1, Vd, M1, Q, M2, Vm2 = decode_opcode(opcode, decode_mask)

            # if !Consistent(M) || !Consistent(Vm) then SEE VORR (register);
            # if Q == '1' && (Vd<0> == '1' || Vm<0> == '1') then UNDEFINED;
            # single_register = FALSE; advsimd = TRUE;
            # d = UInt(D:Vd); m = UInt(M:Vm); regs = if Q == '0' then 1 else 2;
            if M1 != M2 or Vm1 != Vm2:
                return self.decode_vorr_register(opcode, encoding)
            
            if Q == 1 and (get_bit(Vd, 0) == 1 or get_bit(Vm1, 0) == 1):
                raise UndefinedOpcode()
            
            single_register = False
            advsimd = True
            
            d = (D << 4) | Vd
            m = (M1 << 4) | Vm1
            regs = 1 if Q == 0 else 2

        elif encoding == eEncodingA2:
            decode_mask = [4, I5, 1, I6, 4, I3, 1, I2, 1, I1, 4]
            cond, D, Vd, sz, M, Vm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            # single_register = (sz == '0'); advsimd = FALSE;
            # if single_register then
            #     d = UInt(Vd:D); m = UInt(Vm:M);
            # else
            #     d = UInt(D:Vd); m = UInt(M:Vm); regs = 1;
            single_register = sz == 0
            advsimd = False
            if single_register:
                d = (Vd << 1) | D
                m = (Vm << 1) | M
            else:
                d = (D << 4) | Vd
                m = (M << 4) | Vm
                regs = 1

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if encoding in [eEncodingT1, eEncodingA1]:
            if Q == 1:
                # VMOV{<c>}{<q>}{.<dt>} <Qd>, <Qm>    Encoding T1/A1, Q = 1
                qualifier = ".I64"
                operands = [QRegister(d), QRegister(m)]
            
            else:
                # VMOV{<c>}{<q>}{.<dt>} <Dd>, <Dm>    Encoding T1/A1, Q = 0
                qualifier = ".I32"
                operands = [DRegister(d), DRegister(m)]
        
        else:
            if sz == 1:
                # VMOV{<c>}{<q>}.F64 <Dd>, <Dm>       Encoding T2/A2, sz = 1
                qualifier = ".F64"
                operands = [DRegister(d), DRegister(m)]
            
            else:
                # VMOV{<c>}{<q>}.F32 <Sd>, <Sm>       Encoding T2/A2, sz = 0
                qualifier = ".F32"
                operands = [SRegister(d), SRegister(m)]


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vmov_arm_core_register_to_scalar(self, opcode, encoding):
        """
        A8.8.341
        VMOV (ARM core register to scalar)
        This instruction copies a byte, halfword, or word from an ARM core register into an Advanced SIMD scalar.        
        """
        props = {}
        
        name = "VMOV"
        ins_id = ARMInstruction.vmov_arm_core_register_to_scalar
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 2, I1, 4, 4, I4, 1, 2, I5]
            opc1, Vd, Rt, D, opc2 = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [4, I5, 2, I1, 4, 4, I4, 1, 2, I5]
            cond, opc1, Vd, Rt, D, opc2 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        opc = (opc1 << 2) | opc2
        
        if get_bit(opc, 3) == 1:
            advsimd = True
            esize = 8
            index = (get_bit(opc1, 0) << 2) | opc2
            qualifier = ".8"

        elif get_bit(opc, 3) == 0 and get_bit(opc, 0) == 1:
            advsimd = True
            esize = 16
            index = (get_bit(opc1, 0) << 1) | get_bit(opc2, 1)
            qualifier = ".16"
        
        elif get_bit(opc, 3) == 0 and get_bit(opc, 1) == 0 and get_bit(opc, 0) == 0:
            advsimd = False
            esize = 32
            index = get_bit(opc1, 0)
            qualifier = ".32"
        
        elif get_bit(opc, 3) == 0 and get_bit(opc, 1) == 1 and get_bit(opc, 0) == 0:
            raise UndefinedOpcode()
        
        d = (D << 4) | Vd
        
        # if t == 15 || (CurrentInstrSet() != InstrSet_ARM && t == 13) then UNPREDICTABLE;
        if Rt == 15 or (encoding in [eEncodingT1] and Rt == 13):
            raise UnpredictableInstructionException()
        
        operands = [DRegister(d, index), Register(Rt)]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vmov_scalar_to_arm_core_register(self, opcode, encoding):
        """
        A8.8.342
        VMOV (scalar to ARM core register)
        This instruction copies a byte, halfword, or word from an Advanced SIMD scalar to an ARM core register. Bytes
        and halfwords can be either zero-extended or sign-extended.        
        """
        props = {}
        
        name = "VMOV"
        ins_id = ARMInstruction.vmov_scalar_to_arm_core_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I8, 1, 2, I1, 4, 4, I4, 1, 2, I5]
            U, opc1, Vn, Rt, N, opc2 = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [4, I4, 1, 2, I1, 4, 4, I4, 1, 2, I5]
            cond, U, opc1, Vn, Rt, N, opc2 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        U_opc1_opc2 = (U << 4) | (opc1 << 2) | opc2
        
        if get_bit(U_opc1_opc2, 3) == 1:
            advsimd = True
            esize = 8
            index = (get_bit(opc1, 0) << 2) | opc2
        
        elif get_bit(U_opc1_opc2, 3) == 0 and get_bit(U_opc1_opc2, 0) == 1:
            advsimd = True
            esize = 16
            index = (get_bit(opc1, 0) << 1) | get_bit(opc2, 1)
        
        elif (U_opc1_opc2 & 0b11011) == 0b00000:
            advsimd = False
            esize = 32
            index = get_bit(opc1, 0)
        
        elif (U_opc1_opc2 & 0b11011) == 0b10000:
            raise UndefinedOpcode()
        
        elif (U_opc1_opc2 & 0b01011) == 0b00010:
            raise UndefinedOpcode()
        
        # t = UInt(Rt); n = UInt(N:Vn); unsigned = (U == '1');
        n = (N << 4) | Vn
        unsigned = U == 1
        
        qualifier = ".%s%d" % ("U" if unsigned else "S", esize)
        operands = [Register(Rt), DRegister(n, index)]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vmov_between_arm_core_register_and_single_precision_register(self, opcode, encoding):
        """
        A8.8.343
        VMOV (between ARM core register and single-precision register)
        This instruction transfers the contents of a single-precision Floating-point register to an ARM core register, or the
        contents of an ARM core register to a single-precision Floating-point register.        
        """
        props = {}
        
        name = "VMOV"
        ins_id = ARMInstruction.vmov_between_arm_core_register_and_single_precision_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(11), 1, 4, 4, I4, 1, I7]
            op, Vn, Rt, N = decode_opcode(opcode, decode_mask)

        elif encoding == eEncodingA1:
            decode_mask = [4, I7, 1, 4, 4, I4, 1, I7]
            cond, op, Vn, Rt, N = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        # to_arm_register = (op == '1'); t = UInt(Rt); n = UInt(Vn:N);
        # if t == 15 || (CurrentInstrSet() != InstrSet_ARM && t == 13) then UNPREDICTABLE;
        to_arm_register = op == 1
        n = (Vn << 1) | N
        if Rt == 15 or (encoding == eEncodingT1 and Rt == 13):
            raise UnpredictableInstructionException()

        if op == 0:
            operands = [SRegister(n), Register(Rt)]
        
        else:
            operands = [Register(Rt), SRegister(n)]
        
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmov_between_two_arm_core_registers_and_two_single_precision_registers(self, opcode, encoding):
        """
        A8.8.344
        VMOV (between two ARM core registers and two single-precision registers)
        This instruction transfers the contents of two consecutively numbered single-precision Floating-point registers to
        two ARM core registers, or the contents of two ARM core registers to a pair of single-precision Floating-point
        registers. The ARM core registers do not have to be contiguous.        
        """
        props = {}
        
        name = "VMOV"
        ins_id = ARMInstruction.vmov_between_two_arm_core_registers_and_two_single_precision_registers
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(11), 1, 4, 4, I6, 1, I1, 4]
            op, Rt2, Rt, M, Vm = decode_opcode(opcode, decode_mask)

        elif encoding == eEncodingA1:
            decode_mask = [4, I7, 1, 4, 4, I6, 1, I1, 4]
            cond, op, Rt2, Rt, M, Vm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")
        
        # to_arm_registers = (op == '1'); t = UInt(Rt); t2 = UInt(Rt2); m = UInt(Vm:M);
        # if t == 15 || t2 == 15 || m == 31 then UNPREDICTABLE;
        # if CurrentInstrSet() != InstrSet_ARM && (t == 13 || t2 == 13) then UNPREDICTABLE;
        # if to_arm_registers && t == t2 then UNPREDICTABLE;
        
        to_arm_registers = op == 1
        m = (Vm << 1) | M
        if Rt == 15 or Rt2 == 15 or m == 31:
            raise UnpredictableInstructionException()
        
        if encoding == eEncodingT1 and (Rt == 13 or Rt2 == 13):
            raise UnpredictableInstructionException()
        
        if to_arm_registers and Rt == Rt2:
            raise UnpredictableInstructionException()
        
        if op == 0:
            operands = [SRegister(m), SRegister(m + 1), Register(Rt), Register(Rt2)]
        
        else:
            operands = [Register(Rt), Register(Rt2), SRegister(m), SRegister(m + 1)]
        
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmov_between_two_arm_core_registers_and_a_double_word_extension_register(self, opcode, encoding):
        """
        A8.8.345
        VMOV (between two ARM core registers and a doubleword extension register)
        This instruction copies two words from two ARM core registers into a doubleword extension register, or from a
        doubleword extension register to two ARM core registers.        
        """
        props = {}
        
        name = "VMOV"
        ins_id = ARMInstruction.vmov_between_two_arm_core_registers_and_a_double_word_extension_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(11), 1, 4, 4, I6, 1, I1, 4]
            op, Rt2, Rt, M, Vm = decode_opcode(opcode, decode_mask)

        elif encoding == eEncodingA1:
            decode_mask = [4, I7, 1, 4, 4, I6, 1, I1, 4]
            cond, op, Rt2, Rt, M, Vm = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        # to_arm_registers = (op == '1'); t = UInt(Rt); t2 = UInt(Rt2); m = UInt(M:Vm);
        # if t == 15 || t2 == 15 then UNPREDICTABLE;
        # if CurrentInstrSet() != InstrSet_ARM && (t == 13 || t2 == 13) then UNPREDICTABLE;
        # if to_arm_registers && t == t2 then UNPREDICTABLE;
        to_arm_registers = op == 1
        m = (M << 4) | Vm
        if Rt == 15 or Rt2 == 15:
            raise UnpredictableInstructionException()
        
        if encoding == eEncodingT1 and (Rt == 13 or Rt2 == 13):
            raise UnpredictableInstructionException()
        
        if to_arm_registers and Rt == Rt2:
            raise UnpredictableInstructionException()
        
        if op == 0:
            operands = [DRegister(m), Register(Rt), Register(Rt2)]
        
        else:
            operands = [Register(Rt), Register(Rt2), DRegister(m)]


        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmovl(self, opcode, encoding):
        """
        A8.8.346
        VMOVL
        Vector Move Long takes each element in a doubleword vector, sign or zero-extends them to twice their original
        length, and places the results in a quadword vector.        
        """
        props = {}
        
        name = "VMOVL"
        ins_id = ARMInstruction.vmovl
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmovn(self, opcode, encoding):
        """
        A8.8.347
        VMOVN
        Vector Move and Narrow copies the least significant half of each element of a quadword vector into the
        corresponding elements of a doubleword vector.        
        """
        props = {}
        
        name = "VMOVN"
        ins_id = ARMInstruction.vmovn
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmrs(self, opcode, encoding):
        """
        A8.8.348
        VMRS
        Move to ARM core register from Advanced SIMD and Floating-point Extension System Register moves the value
        of the FPSCR to an ARM core register.        
        """
        props = {}
        
        name = "VMRS"
        ins_id = ARMInstruction.vmrs
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(16), 4, I(12)]
            Rt = decode_opcode(opcode, decode_mask)

            # t = UInt(Rt);
            # if t == 13 && CurrentInstrSet() != InstrSet_ARM then UNPREDICTABLE;
            if Rt == 13:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I(12), 4, I(12)]
            cond, Rt = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        operands = [Register(Rt), FPSCR()]
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmsr(self, opcode, encoding):
        """
        A8.8.349
        VMSR
        Move to Advanced SIMD and Floating-point Extension System Register from ARM core register moves the value
        of an ARM core register to the FPSCR.        
        """
        props = {}
        
        name = "VMSR"
        ins_id = ARMInstruction.vmsr
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmul_int(self, opcode, encoding):
        """
        A8.8.350
        VMUL, VMULL (integer and polynomial)
        Vector Multiply multiplies corresponding elements in two vectors. Vector Multiply Long does the same thing, but
        with destination vector elements that are twice as long as the elements that are multiplied.        
        """
        props = {}
        
        name = "VMUL"
        ins_id = ARMInstruction.vmul_int
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmul_fp(self, opcode, encoding):
        """
        A8.8.351
        VMUL (floating-point)
        Vector Multiply multiplies corresponding elements in two vectors, and places the results in the destination vector.        
        """
        props = {}
        
        name = "VMUL"
        ins_id = ARMInstruction.vmul_fp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmul_scalar(self, opcode, encoding):
        """
        A8.8.352
        VMUL, VMULL (by scalar)
        Vector Multiply multiplies each element in a vector by a scalar, and places the results in a second vector. Vector
        Multiply Long does the same thing, but with destination vector elements that are twice as long as the elements that
        are multiplied.        
        """
        props = {}
        
        name = "VMUL"
        ins_id = ARMInstruction.vmul_scalar
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vmvn_immediate(self, opcode, encoding):
        """
        A8.8.353
        VMVN (immediate)
        Vector Bitwise NOT (immediate) places the bitwise inverse of an immediate integer constant into every element of
        the destination register.         
        """
        props = {}
        
        name = "VMVN"
        ins_id = ARMInstruction.vmvn_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I3, 1, I5, 1, I3, 3, 4, 4, I1, 1, I2, 4]
            i, D, imm3, Vd, cmode, Q, imm4 = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I7, 1, I1, 1, I3, 3, 4, 4, I1, 1, I2, 4]
            i, D, imm3, Vd, cmode, Q, imm4 = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if (get_bit(cmode, 0) == 1 and get_bits(cmode, 3, 2) != 0b11) or get_bits(cmode, 3, 2) == 0b111:
            raise RuntimeError("SEE Related encodings")

        if Q == 1 and get_bit(Vd, 0) == 1:
            raise UndefinedOpcode()

        imm64 = AdvSIMDExpandImm(1, cmode, (i << 7) | (imm3 << 4) | imm4)
        d = (D << 4) | Vd
        regs = 1 if Q == 0 else 2

        if Q == 1:
            operands = [QRegister(d), Immediate(imm64)]
            qualifier = ".I64"

        else:
            operands = [DRegister(d), Immediate(imm64)]
            qualifier = ".I32"

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vmvn_register(self, opcode, encoding):
        """
        A8.8.354
        VMVN (register)
        Vector Bitwise NOT (register) takes a value from a register, inverts the value of each bit, and places the result in the
        destination register. The registers can be either doubleword or quadword.        
        """
        props = {}
        
        name = "VMVN"
        ins_id = ARMInstruction.vmvn_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vneg(self, opcode, encoding):
        """
        A8.8.355
        VNEG
        Vector Negate negates each element in a vector, and places the results in a second vector. The floating-point version
        only inverts the sign bit.        
        """
        props = {}
        
        name = "VNEG"
        ins_id = ARMInstruction.vneg
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vnmla_vnmls_vnmul(self, opcode, encoding):
        """
        A8.8.356
        VNMLA, VNMLS, VNMUL
        VNMLA multiplies together two floating-point register values, adds the negation of the floating-point value in the
        destination register to the negation of the product, and writes the result back to the destination register.        
        """
        props = {}
        
        name = "VNMLA"
        ins_id = ARMInstruction.vnmla_vnmls_vnmul
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vorn_register(self, opcode, encoding):
        """
        A8.8.358
        VORN (register)
        This instruction performs a bitwise OR NOT operation between two registers, and places the result in the destination
        register. The operand and result registers can be quadword or doubleword. They must all be the same size.        
        """
        props = {}
        
        name = "VORN"
        ins_id = ARMInstruction.vorn_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vorr_immediate(self, opcode, encoding):
        """
        A8.8.359
        VORR (immediate)
        This instruction takes the contents of the destination vector, performs a bitwise OR with an immediate constant, and
        returns the result into the destination vector. For the range of constants available, see One register and a modified
        immediate value on page A7-267.        
        """
        props = {}
        
        name = "VORR"
        ins_id = ARMInstruction.vorr_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I3, 1, I5, 1, I3, 3, 4, 4, I1, 1, I2, 4]
            i, D, imm3, Vd, cmode, Q, imm4 = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I7, 1, I1, 1, I3, 3, 4, 4, I1, 1, I2, 4]
            i, D, imm3, Vd, cmode, Q, imm4 = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if get_bit(cmode, 0) == 0 or get_bits(cmode, 3, 2) == 0b11:
            return self.decode_vmov_immediate(opcode, encoding)

        if Q == 1 and get_bit(Vd, 0) == 1:
            raise UndefinedOpcode()

        imm64 = AdvSIMDExpandImm(0, cmode, ((i << 7) | (imm3 << 4) | imm4))
        d = (D << 4) | Vd
        regs = 1 if Q == 0 else 2

        if Q == 1:
            qualifier = ".64"
            if regs == 1:
                operands = [QRegister(d), Immediate(imm64)]
            else:
                operands = [QRegister(d), QRegister(d), Immediate(imm64)]
        else:
            qualifier = ".32"
            if regs == 1:
                operands = [DRegister(d), Immediate(imm64)]
            else:
                operands = [DRegister(d), DRegister(d), Immediate(imm64)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vorr_register(self, opcode, encoding):
        """
        A8.8.360
        VORR (register)
        This instruction performs a bitwise OR operation between two registers, and places the result in the destination
        register. The operand and result registers can be quadword or doubleword. They must all be the same size      
        """
        props = {}
        
        name = "VORR"
        ins_id = ARMInstruction.vorr_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 1, I2, 4, 4, I4, 1, 1, 1, I1, 4]
            D, Vn, Vd, N, Q, M, Vm = decode_opcode(opcode, decode_mask)

        elif encoding == eEncodingA1:
            decode_mask = [I9, 1, I2, 4, 4, I4, 1, 1, 1, I1, 4]
            D, Vn, Vd, N, Q, M, Vm = decode_opcode(opcode, decode_mask)

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if N == M and Vn == Vm:
            return self.decode_vmov_register(opcode, encoding)

        if Q == 1 and (get_bit(Vd, 0) == 1 or get_bit(Vn, 0) == 1 or get_bit(Vm, 0) == 1):
            raise UndefinedOpcode()

        d = (D << 4) | Vd
        n = (N << 4) | Vn
        m = (M << 4) | Vm
        regs = 1 if Q == 0 else 2

        if Q == 1:
            qualifier = ".64"
            if regs == 1:
                operands = [QRegister(n), QRegister(m)]
            else:
                operands = [QRegister(d), QRegister(n), QRegister(m)]
        else:
            qualifier = ".32"
            if regs == 1:
                operands = [DRegister(n), DRegister(m)]
            else:
                operands = [DRegister(d), DRegister(n), DRegister(m)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vpadal(self, opcode, encoding):
        """
        A8.8.361
        VPADAL
        Vector Pairwise Add and Accumulate Long adds adjacent pairs of elements of a vector, and accumulates the results
        into the elements of the destination vector.        
        """
        props = {}
        
        name = "VPADAL"
        ins_id = ARMInstruction.vpadal
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vpadd_int(self, opcode, encoding):
        """
        A8.8.362
        VPADD (integer)
        Vector Pairwise Add (integer) adds adjacent pairs of elements of two vectors, and places the results in the destination
        vector.        
        """
        props = {}
        
        name = "VPADD"
        ins_id = ARMInstruction.vpadd_int
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vpadd_fp(self, opcode, encoding):
        """
        A8.8.363
        VPADD (floating-point)
        Vector Pairwise Add (floating-point) adds adjacent pairs of elements of two vectors, and places the results in the
        destination vector.        
        """
        props = {}
        
        name = "VPADD"
        ins_id = ARMInstruction.vpadd_fp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vpaddl(self, opcode, encoding):
        """
        A8.8.364
        VPADDL
        Vector Pairwise Add Long adds adjacent pairs of elements of two vectors, and places the results in the destination
        vector.        
        """
        props = {}
        
        name = "VPADDL"
        ins_id = ARMInstruction.vpaddl
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vpmax_vpmin_int(self, opcode, encoding):
        """
        A8.8.365
        VPMAX, VPMIN (integer)
        Vector Pairwise Maximum compares adjacent pairs of elements in two doubleword vectors, and copies the larger
        of each pair into the corresponding element in the destination doubleword vector.        
        """
        props = {}
        
        name = "VPMAX"
        ins_id = ARMInstruction.vpmax_vpmin_int
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vpmax_vpmin_fp(self, opcode, encoding):
        """
        A8.8.366
        VPMAX, VPMIN (floating-point)
        Vector Pairwise Maximum compares adjacent pairs of elements in two doubleword vectors, and copies the larger
        of each pair into the corresponding element in the destination doubleword vector.        
        """
        props = {}
        
        name = "VPMAX"
        ins_id = ARMInstruction.vpmax_vpmin_fp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vpop(self, opcode, encoding):
        """
        A8.8.367
        VPOP
        Vector Pop loads multiple consecutive extension registers from the stack.        
        """
        props = {}
        
        name = "VPOP"
        ins_id = ARMInstruction.vpop
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 1, I6, 4, I4, 8]
            D, Vd, imm8 = decode_opcode(opcode, decode_mask)
            single_regs = False
            d = (D << 4) | Vd
            imm32 = imm8 << 2
            regs = imm8 / 2

            if imm8 % 2:
                raise RuntimeError("SEE FLDMX")

            if regs == 0 or regs > 16 or (d + regs) > 32:
                raise UnpredictableInstructionException()

            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I9, 1, I6, 4, I4, 8]
            D, Vd, imm8 = decode_opcode(opcode, decode_mask)
            single_regs = True
            d = (Vd << 1) | D
            imm32 = imm8 << 2
            regs = imm8

            if regs == 0 or (d + regs) > 32:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA1:
            decode_mask = [4, I5, 1, I6, 4, I4, 8]
            cond, D, Vd, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            single_regs = False
            d = (D << 4) | Vd
            imm32 = imm8 << 2
            regs = imm8 / 2
            if imm8 % 2:
                raise RuntimeError("SEE FLDMX")

            if regs == 0 or regs > 16 or (d + regs) > 32:
                raise UnpredictableInstructionException()

        elif encoding == eEncodingA2:
            decode_mask = [4, I5, 1, I6, 4, I4, 8]
            cond, D, Vd, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            single_regs = True
            d = (Vd << 1) | D
            imm32 = imm8 << 2
            regs = imm8

            if regs == 0 or (d + regs) > 32:
                raise UnpredictableInstructionException()

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        qualifier = ".32" if single_regs else ".64"

        operands = []
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vpush(self, opcode, encoding):
        """
        A8.8.368
        VPUSH
        Vector Push stores multiple consecutive extension registers to the stack.        
        """
        props = {}
        
        name = "VPUSH"
        ins_id = ARMInstruction.vpush
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 1, I6, 4, I4, 8]
            D, Vd, imm8 = decode_opcode(opcode, decode_mask)
            single_regs = False
            d = (D << 4) | Vd
            imm32 = imm8 << 2
            regs = imm8 / 2
            if imm8 % 2:
                raise RuntimeError("SEE FSTMX")

            if regs == 0 or regs > 16 or (d + regs) > 32:
                raise UnpredictableInstructionException()                

        elif encoding == eEncodingT2:
            decode_mask = [I9, 1, I6, 4, I4, 8]
            D, Vd, imm8 = decode_opcode(opcode, decode_mask)
            single_regs = True
            d = (Vd << 1) | D
            imm32 = imm8 << 2
            regs = imm8
            if regs == 0 or (d + regs) > 32:
                raise UnpredictableInstructionException()            

        elif encoding == eEncodingA1:
            decode_mask = [4, I5, 1, I6, 4, I4, 8]
            cond, D, Vd, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            single_regs = False
            d = (D << 4) | Vd
            imm32 = imm8 << 2
            regs = imm8 / 2
            if imm8 % 2:
                raise RuntimeError("SEE FSTMX")

            if regs == 0 or regs > 16 or (d + regs) > 32:
                raise UnpredictableInstructionException()                

        elif encoding == eEncodingA2:
            decode_mask = [4, I5, 1, I6, 4, I4, 8]
            cond, D, Vd, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)
            single_regs = True
            d = (Vd << 1) | D
            imm32 = imm8 << 2
            regs = imm8
            if regs == 0 or (d + regs) > 32:
                raise UnpredictableInstructionException()            

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        qualifier = ".32" if single_regs else ".64"
        operands = []
        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding, qualifier)
        return ins

    def decode_vqabs(self, opcode, encoding):
        """
        A8.8.369
        VQABS
        Vector Saturating Absolute takes the absolute value of each element in a vector, and places the results in the
        destination vector.        
        """
        props = {}
        
        name = "VQABS"
        ins_id = ARMInstruction.vqabs
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqadd(self, opcode, encoding):
        """
        A8.8.370
        VQADD
        Vector Saturating Add adds the values of corresponding elements of two vectors, and places the results in the
        destination vector.        
        """
        props = {}
        
        name = "VQADD"
        ins_id = ARMInstruction.vqadd
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqdmlal_vqdmlsl(self, opcode, encoding):
        """
        A8.8.371
        VQDMLAL, VQDMLSL
        Vector Saturating Doubling Multiply Accumulate Long multiplies corresponding elements in two doubleword
        vectors, doubles the products, and accumulates the results into the elements of a quadword vector.        
        """
        props = {}
        
        name = "VQDMLAL"
        ins_id = ARMInstruction.vqdmlal_vqdmlsl
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqdmulh(self, opcode, encoding):
        """
        A8.8.372
        VQDMULH
        Vector Saturating Doubling Multiply Returning High Half multiplies corresponding elements in two vectors,
        doubles the results, and places the most significant half of the final results in the destination vector. The results are
        truncated (for rounded results see VQRDMULH on page A8-1006).        
        """
        props = {}
        
        name = "VQDMULH"
        ins_id = ARMInstruction.vqdmulh
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqdmull(self, opcode, encoding):
        """
        A8.8.373
        VQDMULL
        Vector Saturating Doubling Multiply Long multiplies corresponding elements in two doubleword vectors, doubles
        the products, and places the results in a quadword vector.        
        """
        props = {}
        name = "VQDMULL"
        ins_id = ARMInstruction.vqdmull
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqmovn_vqmovun(self, opcode, encoding):
        """
        A8.8.374
        VQMOVN, VQMOVUN
        Vector Saturating Move and Narrow copies each element of the operand vector to the corresponding element of the
        destination vector.        
        """
        props = {}
        
        name = "VQMOVN"
        ins_id = ARMInstruction.vqmovn_vqmovun
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqneg(self, opcode, encoding):
        """
        A8.8.375
        VQNEG
        Vector Saturating Negate negates each element in a vector, and places the results in the destination vector.        
        """
        props = {}
        
        name = "VQNEG"
        ins_id = ARMInstruction.vqneg
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqrdmulh(self, opcode, encoding):
        """
        A8.8.376
        VQRDMULH
        Vector Saturating Rounding Doubling Multiply Returning High Half multiplies corresponding elements in two
        vectors, doubles the results, and places the most significant half of the final results in the destination vector.         
        """
        props = {}
        
        name = "VQRDMULH"
        ins_id = ARMInstruction.vqrdmulh
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqrshl(self, opcode, encoding):
        """
        A8.8.377
        VQRSHL
        Vector Saturating Rounding Shift Left takes each element in a vector, shifts them by a value from the least
        significant byte of the corresponding element of a second vector, and places the results in the destination vector. If
        the shift value is positive, the operation is a left shift. Otherwise, it is a right shift.        
        """
        props = {}
        
        name = "VQRSHL"
        ins_id = ARMInstruction.vqrshl
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqrshrn_vqrshrun(self, opcode, encoding):
        """
        A8.8.378
        VQRSHRN, VQRSHRUN
        Vector Saturating Rounding Shift Right, Narrow takes each element in a quadword vector of integers, right shifts
        them by an immediate value, and places the rounded results in a doubleword vector.        
        """
        props = {}
        
        name = "VQRSHRN"
        ins_id = ARMInstruction.vqrshrn_vqrshrun
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqshl_register(self, opcode, encoding):
        """
        A8.8.379
        VQSHL (register)
        Vector Saturating Shift Left (register) takes each element in a vector, shifts them by a value from the least significant
        byte of the corresponding element of a second vector, and places the results in the destination vector. If the shift
        value is positive, the operation is a left shift. Otherwise, it is a right shift        
        """
        props = {}
        
        name = "VQSHL"
        ins_id = ARMInstruction.vqshl_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqshl_vqshlu_immediate(self, opcode, encoding):
        """
        A8.8.380
        VQSHL, VQSHLU (immediate)
        Vector Saturating Shift Left (immediate) takes each element in a vector of integers, left shifts them by an immediate
        value, and places the results in a second vector.        
        """
        props = {}
        
        name = "VQSHL"
        ins_id = ARMInstruction.vqshl_vqshlu_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqshrn_vqshrun(self, opcode, encoding):
        """
        A8.8.381
        VQSHRN, VQSHRUN
        Vector Saturating Shift Right, Narrow takes each element in a quadword vector of integers, right shifts them by an
        immediate value, and places the truncated results in a doubleword vector.        
        """
        props = {}
        
        name = "VQSHRN"
        ins_id = ARMInstruction.vqshrn_vqshrun
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vqsub(self, opcode, encoding):
        """
        A8.8.382
        VQSUB
        Vector Saturating Subtract subtracts the elements of the second operand vector from the corresponding elements of
        the first operand vector, and places the results in the destination vector. Signed and unsigned operations are distinct.
        """
        props = {}
        
        name = "VQSUB"
        ins_id = ARMInstruction.vqsub
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vraddhn(self, opcode, encoding):
        """
        A8.8.383
        VRADDHN
        Vector Rounding Add and Narrow, returning High Half adds corresponding elements in two quadword vectors, and
        places the most significant half of each result in a doubleword vector. The results are rounded. (For truncated results,
        see VADDHN on page A8-830.)        
        """
        props = {}
        
        name = "VRADDHN"
        ins_id = ARMInstruction.vraddhn
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrecpe(self, opcode, encoding):
        """
        A8.8.384
        VRECPE
        Vector Reciprocal Estimate finds an approximate reciprocal of each element in the operand vector, and places the
        results in the destination vector.        
        """
        props = {}
        
        name = "VRECPE"
        ins_id = ARMInstruction.vrecpe
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrecps(self, opcode, encoding):
        """
        A8.8.385
        VRECPS
        Vector Reciprocal Step multiplies the elements of one vector by the corresponding elements of another vector,
        subtracts each of the products from 2.0, and places the results into the elements of the destination vector.        
        """
        props = {}
        
        name = "VRECPS"
        ins_id = ARMInstruction.vrecps
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrev(self, opcode, encoding):
        """
        A8.8.386
        VREV16, VREV32, VREV64
        VREV16 (Vector Reverse in halfwords) reverses the order of 8-bit elements in each halfword of the vector, and places
        the result in the corresponding destination vector.        
        """
        props = {}
        
        name = "VREV16"
        ins_id = ARMInstruction.vrev
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrhadd(self, opcode, encoding):
        """
        A8.8.387
        VRHADD
        Vector Rounding Halving Add adds corresponding elements in two vectors of integers, shifts each result right one
        bit, and places the final results in the destination vector.        
        """
        props = {}
        
        name = "VRHADD"
        ins_id = ARMInstruction.vrhadd
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrshl(self, opcode, encoding):
        """
        A8.8.388
        VRSHL
        Vector Rounding Shift Left takes each element in a vector, shifts them by a value from the least significant byte of
        the corresponding element of a second vector, and places the results in the destination vector. If the shift value is
        positive, the operation is a left shift. If the shift value is negative, it is a rounding right shift.        
        """
        props = {}
        
        name = "VRSHL"
        ins_id = ARMInstruction.vrshl
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrshr(self, opcode, encoding):
        """
        A8.8.389
        VRSHR
        Vector Rounding Shift Right takes each element in a vector, right shifts them by an immediate value, and places the
        rounded results in the destination vector. For truncated results, see VSHR on page A8-1050.        
        """
        props = {}
        
        name = "VRSHR"
        ins_id = ARMInstruction.vrshr
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrshrn(self, opcode, encoding):
        """
        A8.8.390
        VRSHRN
        Vector Rounding Shift Right and Narrow takes each element in a vector, right shifts them by an immediate value,
        and places the rounded results in the destination vector. For truncated results, see VSHRN on page A8-1052.        
        """
        props = {}
        
        name = "VRSHRN"
        ins_id = ARMInstruction.vrshrn
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrsqrte(self, opcode, encoding):
        """
        A8.8.391
        VRSQRTE
        Vector Reciprocal Square Root Estimate finds an approximate reciprocal square root of each element in a vector,
        and places the results in a second vector.        
        """
        props = {}
        
        name = "VRSQRTE"
        ins_id = ARMInstruction.vrsqrte
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrsqrts(self, opcode, encoding):
        """
        A8.8.392
        VRSQRTS
        Vector Reciprocal Square Root Step multiplies the elements of one vector by the corresponding elements of another
        vector, subtracts each of the products from 3.0, divides these results by 2.0, and places the results into the elements
        of the destination vector.        
        """
        props = {}
        
        name = "VRSQRTS"
        ins_id = ARMInstruction.vrsqrts
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrsra(self, opcode, encoding):
        """
        A8.8.393
        VRSRA
        Vector Rounding Shift Right and Accumulate takes each element in a vector, right shifts them by an immediate
        value, and accumulates the rounded results into the destination vector. (For truncated results, see VSRA on
        page A8-1058.)        
        """
        props = {}
        
        name = "VRSRA"
        ins_id = ARMInstruction.vrsra
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vrsubhn(self, opcode, encoding):
        """
        A8.8.394
        VRSUBHN
        Vector Rounding Subtract and Narrow, returning High Half subtracts the elements of one quadword vector from the
        corresponding elements of another quadword vector takes the most significant half of each result, and places the
        final results in a doubleword vector. The results are rounded. (For truncated results, see VSUBHN on
        page A8-1086.)        
        """
        props = {}
        
        name = "VRSUBHN"
        ins_id = ARMInstruction.vrsubhn
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vshl_immediate(self, opcode, encoding):
        """
        A8.8.395
        VSHL (immediate)
        Vector Shift Left (immediate) takes each element in a vector of integers, left shifts them by an immediate value, and
        places the results in the destination vector.        
        """
        props = {}
        
        name = "VSHL"
        ins_id = ARMInstruction.vshl_immediate
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vshl_register(self, opcode, encoding):
        """
        A8.8.396
        VSHL (register)
        Vector Shift Left (register) takes each element in a vector, shifts them by a value from the least significant byte of
        the corresponding element of a second vector, and places the results in the destination vector. If the shift value is
        positive, the operation is a left shift. If the shift value is negative, it is a truncating right shift.        
        """
        props = {}
        
        name = "VSHL"
        ins_id = ARMInstruction.vshl_register
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vshll(self, opcode, encoding):
        """
        A8.8.397
        VSHLL
        Vector Shift Left Long takes each element in a doubleword vector, left shifts them by an immediate value, and places
        the results in a quadword vector.        
        """
        props = {}
        
        name = "VSHLL"
        ins_id = ARMInstruction.vshll
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vshr(self, opcode, encoding):
        """
        A8.8.398
        VSHR
        Vector Shift Right takes each element in a vector, right shifts them by an immediate value, and places the truncated
        results in the destination vector.        
        """
        props = {}
        
        name = "VSHR"
        ins_id = ARMInstruction.vshr
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vshrn(self, opcode, encoding):
        """
        A8.8.399
        VSHRN
        Vector Shift Right Narrow takes each element in a vector, right shifts them by an immediate value, and places the
        truncated results in the destination vector.         
        """
        props = {}
        
        name = "VSHRN"
        ins_id = ARMInstruction.vshrn
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vsli(self, opcode, encoding):
        """
        A8.8.400
        VSLI
        Vector Shift Left and Insert takes each element in the operand vector, left shifts them by an immediate value, and
        inserts the results in the destination vector. Bits shifted out of the left of each element are lost.        
        """
        props = {}
        
        name = "VSLI"
        ins_id = ARMInstruction.vsli
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vsqrt(self, opcode, encoding):
        """
        A8.8.401
        VSQRT
        This instruction calculates the square root of the value in a floating-point register and writes the result to another
        floating-point register.        
        """
        props = {}
        
        name = "VSQRT"
        ins_id = ARMInstruction.vsqrt
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vsra(self, opcode, encoding):
        """
        A8.8.402
        VSRA
        Vector Shift Right and Accumulate takes each element in a vector, right shifts them by an immediate value, and
        accumulates the truncated results into the destination vector.
        """
        props = {}
        
        name = "VSRA"
        ins_id = ARMInstruction.vsra
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vsri(self, opcode, encoding):
        """
        A8.8.403
        VSRI
        Vector Shift Right and Insert takes each element in the operand vector, right shifts them by an immediate value, and
        inserts the results in the destination vector. Bits shifted out of the right of each element are lost.        
        """
        props = {}
        
        name = "VSRI"
        ins_id = ARMInstruction.vsri
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vstm(self, opcode, encoding):
        """
        A8.8.412
        VSTM
        Vector Store Multiple stores multiple extension registers to consecutive memory locations using an address from an
        ARM core register.        
        """
        props = {}
        
        name = "VSTM"
        ins_id = ARMInstruction.vstm
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vstr(self, opcode, encoding):
        """
        A8.8.413
        VSTR
        This instruction stores a single extension register to memory, using an address from an ARM core register, with an
        optional offset.
        """
        props = {}
        
        name = "VSTR"
        ins_id = ARMInstruction.vstr
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I8, 1, 1, I2, 4, 4, I4, 8]
            U, D, Rn, Vd, imm8 = decode_opcode(opcode, decode_mask)

            # single_reg = FALSE; add = (U == '1'); imm32 = ZeroExtend(imm8:'00', 32);
            single_reg = False
            add = U == 1
            imm32 = imm8 << 2

            # d = UInt(D:Vd); n = UInt(Rn);
            Sd = (D << 4) | Vd
            Sn = Rn

            # if n == 15 && CurrentInstrSet() != InstrSet_ARM then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()
            
            operands = [DRegister(Sd), Memory(Register(Rn), Immediate(imm32))]

        elif encoding == eEncodingT2:
            decode_mask = [I8, 1, 1, I2, 4, 4, I4, 8]
            U, D, Rn, Vd, imm8 = decode_opcode(opcode, decode_mask)

            # single_reg = TRUE; add = (U == '1'); imm32 = ZeroExtend(imm8:'00', 32);
            single_reg = True
            add = U == 1
            imm32 = imm8 << 2

            # d = UInt(Vd:D); n = UInt(Rn);
            Sd = (Vd << 1) | D
            Sn = Rn

            # if n == 15 && CurrentInstrSet() != InstrSet_ARM then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()        
            
            operands = [SRegister(Sd), Memory(Register(Rn), Immediate(imm32))]

        elif encoding == eEncodingA1:
            decode_mask = [4, I4, 1, 1, I2, 4, 4, I4, 8]
            cond, U, D, Rn, Vd, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            # single_reg = FALSE; add = (U == '1'); imm32 = ZeroExtend(imm8:'00', 32);
            single_reg = False
            add = U == 1
            imm32 = imm8 << 2

            # d = UInt(D:Vd); n = UInt(Rn);
            Sd = (D << 4) | Vd
            Sn = Rn

            # if n == 15 && CurrentInstrSet() != InstrSet_ARM then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()
            
            operands = [DRegister(Sd), Memory(Register(Rn), Immediate(imm32))]

        elif encoding == eEncodingA2:
            decode_mask = [4, I4, 1, 1, I2, 4, 4, I4, 8]
            cond, U, D, Rn, Vd, imm8 = decode_opcode(opcode, decode_mask)
            condition = Condition(cond)

            # single_reg = TRUE; add = (U == '1'); imm32 = ZeroExtend(imm8:'00', 32);
            single_reg = True
            add = U == 1
            imm32 = imm8 << 2

            # d = UInt(Vd:D); n = UInt(Rn);
            Sd = (Vd << 1) | D
            Sn = Rn

            # if n == 15 && CurrentInstrSet() != InstrSet_ARM then UNPREDICTABLE;
            if Rn == 15:
                raise UnpredictableInstructionException()            

            operands = [SRegister(Sd), Memory(Register(Rn), Immediate(imm32))]

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if not add:
            imm32 *= -1

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vsub_int(self, opcode, encoding):
        """
        A8.8.414
        VSUB (integer)
        Vector Subtract subtracts the elements of one vector from the corresponding elements of another vector, and places
        the results in the destination vector.        
        """
        props = {}
        
        name = "VSUB"
        ins_id = ARMInstruction.vsub_int
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vsub_fp(self, opcode, encoding):
        """
        A8.8.415
        VSUB (floating-point)
        Vector Subtract subtracts the elements of one vector from the corresponding elements of another vector, and places
        the results in the destination vector.        
        """
        props = {}
        
        name = "VSUB"
        ins_id = ARMInstruction.vsub_fp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingT2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA2:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vsubhn(self, opcode, encoding):
        """
        A8.8.416
        VSUBHN
        Vector Subtract and Narrow, returning High Half subtracts the elements of one quadword vector from the
        corresponding elements of another quadword vector, takes the most significant half of each result, and places the
        final results in a doubleword vector.         
        """
        props = {}
        
        name = "VSUBHN"
        ins_id = ARMInstruction.vsubhn
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vsubl_vsubw(self, opcode, encoding):
        """
        A8.8.417
        VSUBL, VSUBW
        Vector Subtract Long subtracts the elements of one doubleword vector from the corresponding elements of another
        doubleword vector, and places the results in a quadword vector. Before subtracting, it sign-extends or zero-extends
        the elements of both operands.        
        """
        props = {}
        
        name = "VSUBL"
        ins_id = ARMInstruction.vsubl_vsubw
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vswp(self, opcode, encoding):
        """
        A8.8.418
        VSWP
        VSWP (Vector Swap) exchanges the contents of two vectors. The vectors can be either doubleword or quadword.
        There is no distinction between data types.        
        """
        props = {}
        
        name = "VSWP"
        ins_id = ARMInstruction.vswp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I9, 1, I2, 2, I2, 4, I5, 1, 1, I1, 4]
            D, size, Vd, Q, M, Vm = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I9, 1, I2, 2, I2, 4, I5, 1, 1, I1, 4]
            D, size, Vd, Q, M, Vm = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        if size != 0b00:
            raise UndefinedOpcode()

        if Q == 1 and (get_bit(Vd, 0) == 1 or get_bit(Vm, 0) == 1):
            raise UndefinedOpcode()

        d = (D << 4) | Vd
        m = (M << 4) | Vm

        regs = 1 if Q == 0 else 2

        if Q == 1:
            qualifier = ".64"
            operands = [QRegister(d), QRegister(m)]
        else:
            qualifier = ".32"
            operands = [DRegister(d), DRegister(m)]

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vtbl_vtbx(self, opcode, encoding):
        """
        A8.8.419
        VTBL, VTBX
        Vector Table Lookup uses byte indexes in a control vector to look up byte values in a table and generate a new
        vector. Indexes out of range return 0.        
        """
        props = {}
        
        name = "VTBL"
        ins_id = ARMInstruction.vtbl_vtbx
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vtrn(self, opcode, encoding):
        """
        A8.8.420
        VTRN
        Vector Transpose treats the elements of its operand vectors as elements of 2 x 2 matrices, and transposes the
        matrices.        
        """
        props = {}
        
        name = "VTRN"
        ins_id = ARMInstruction.vtrn
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vtst(self, opcode, encoding):
        """
        A8.8.421
        VTST
        Vector Test Bits takes each element in a vector, and bitwise ANDs it with the corresponding element of a second
        vector. If the result is not zero, the corresponding element in the destination vector is set to all ones. Otherwise, it is
        set to all zeros.        
        """
        props = {}
        
        name = "VTST"
        ins_id = ARMInstruction.vtst
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vuzp(self, opcode, encoding):
        """
        A8.8.422
        VUZP
        Vector Unzip de-interleaves the elements of two vectors. See Table A8-12 and Table A8-13 for examples of the
        operation.        
        """
        props = {}
        
        name = "VUZP"
        ins_id = ARMInstruction.vuzp
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

    def decode_vzip(self, opcode, encoding):
        """
        A8.8.423
        VZIP
        Vector Zip interleaves the elements of two vectors. See Table A8-14 and Table A8-15 for examples of the operation.
        """
        props = {}
        
        name = "VZIP"
        ins_id = ARMInstruction.vzip
        setsflags = False
        condition = None

        if encoding == eEncodingT1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        elif encoding == eEncodingA1:
            decode_mask = [I(0)]
            _ = decode_opcode(opcode, decode_mask)
            operands = []

        else:
            raise InvalidInstructionEncoding("Invalid encoding for instruction")

        ins = Instruction(ins_id, opcode, name, setsflags, condition, operands, encoding)
        return ins

if __name__ == "__main__":
    d = ARMDisassembler()
    print d.disassemble(0xec5cb9ed)