'''
Created on Jun 12, 2013

@author: anon
'''
from disassembler.utils.bits import get_bit, get_bits, ror
from disassembler.constants.arm import *

def DecodeRegShift(type_):
    if type_ == 0:
        return SRType_LSL
    elif type_ == 1:
        return SRType_LSR
    elif type_ == 2:
        return SRType_ASR
    elif type_ == 3:
        return SRType_ROR

    return SRType_Invalid

# A8.6.35 CMP (register) -- Encoding T3
# Convenience function.
def DecodeImmShiftThumb(opcode):
    return DecodeImmShift(get_bits(opcode, 5, 4), get_bits(opcode, 14, 12) << 2 | get_bits(opcode, 7, 6))

# A8.6.35 CMP (register) -- Encoding A1
# Convenience function.
def DecodeImmShiftARM(opcode):
    return DecodeImmShift(get_bits(opcode, 6, 5), get_bits(opcode, 11, 7))

# TODO: Falta esta
# def Decode_ImmShift(shift_t, imm5):
#     ARM_ShifterType dont_care;
#     return Decode_ImmShift(shift_t, imm5, dont_care);

def DecodeImmShift(type_, imm5):
    if type_ == 0:
        return (SRType_LSL, imm5)
    
    elif type_ == 1:
        if imm5 == 0:
            return (SRType_LSR, 32)
        return (SRType_LSR, imm5)

    elif type_ == 2:
        if imm5 == 0:
            return (SRType_ASR, 32)
        return (SRType_ASR, imm5)

    elif type_ == 3:
        if imm5 == 0:
            return (SRType_RRX, 1)
        return (SRType_ROR, imm5)

    return (SRType_Invalid, -1)


# (imm32, carry_out) = ThumbExpandImm_C(imm12, carry_in)
def ThumbExpandImm_C(opcode, carry_in):
    i = get_bit(opcode, 26)
    imm3 = get_bits(opcode, 14, 12)
    abcdefgh = get_bits(opcode, 7, 0)
    imm12 = i << 11 | imm3 << 8 | abcdefgh

    if (get_bits(imm12, 11, 10) == 0):
        
        c = get_bits(imm12, 9, 8)
        if c == 0:
            imm32 = abcdefgh
        elif c == 1:
            imm32 = abcdefgh << 16 | abcdefgh
        elif c == 2:
            imm32 = abcdefgh << 24 | abcdefgh << 8;
        elif c == 3:
            imm32 = abcdefgh << 24 | abcdefgh << 16 | abcdefgh << 8 | abcdefgh 

        carry_out = carry_in
    else:
        unrotated_value = 0x80 | get_bits(imm12, 6, 0)
        imm32 = ror(unrotated_value, 32, get_bits(imm12, 11, 7))
        carry_out = get_bit(imm32, 31)

    return (imm32, carry_out)

# (imm32, carry_out) = ARMExpandImm_C(imm12, carry_in)
def ARMExpandImm_C(opcode, carry_in):
    imm = get_bits(opcode, 7, 0)
    amt = 2 * get_bits(opcode, 11, 8)
    if (amt == 0):
        imm32 = imm
        carry_out = carry_in
    else:
        imm32 = ror(imm, 32, amt)
        carry_out = get_bit(imm32, 31)

    return (imm32, carry_out)

def ThumbExpandImm(opcode):
    imm32, carry_out = ThumbExpandImm_C(opcode, 0) 
    return imm32

def ThumbImm12(opcode):
    i = get_bit(opcode, 26)
    imm3 = get_bits(opcode, 14, 12)
    imm8 = get_bits(opcode, 7, 0)
    imm12 = i << 11 | imm3 << 8 | imm8
    return imm12

def ARMExpandImm(opcode):
    imm32, carry_out = ARMExpandImm_C(opcode, 0)
    return imm32

def BadReg(n):
    return n in [13, 15]
