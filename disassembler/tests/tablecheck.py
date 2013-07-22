'''
Created on Jun 11, 2013

@author: anon
'''
import sys
from emulator.ARMEmulator import ARMEmulator
from emulator.memory import DummyMemoryMap
sys.path.append("../../")

from disassembler.arm import ARMDisassembler
from disassembler.arch import UndefinedOpcode, InvalidInstructionEncoding
from disassembler.arch import UnpredictableInstructionException, InstructionNotImplementedException

import random
import objdump
import llvm

def get_masked_random(mask, value, mode):
    r = random.getrandbits(32)
    
    for i in xrange(0, 32):
        if mask & (1 << i):
            if value & (1 << i):
                r |= value & (1 << i)
            else:
                r &= ~(1 << i)

    # if thumb return half-dword
    # if not mode:
    #    return r & 0xffff
    
    return r

# mask, value = (0xfffffe00, 0x00001800)
# for i in xrange(0, 100):
#     print hex(get_masked_random(mask, value, 0))
#  
# sys.exit()

arm_opcodes = \
(
    # ADC (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x02a00000),

    # ADC (register),, ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x00a00000),

    # ADC (register-shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x00a00010),

    # ADD (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x02800000),

    # ADD (register, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x00800000),

    # ADD (register-shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x00800010),

    # ADR ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fff0000, 0x028f0000),

    # ADR ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fff0000, 0x024f0000),

    # AND (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x02000000),

    # AND (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x00000000),

    # AND (register-shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x00000010),

    # ASR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0070, 0x01a00040),

    # ASR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef00f0, 0x01a00050),

    # BIC (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x03c00000),

    # BIC (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x01c00000),

    # BIC (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x01c00010),

    # BKPT ARMv5TAll | ARMv6All | ARMv7
    (0x0ff000f0, 0x01200070),

    # eEncodingA2 must be placed before eEncodingA1
    # BL, BLX (immediate) ARMv5TAll | ARMv6All | ARMv7
    (0xfe000000, 0xfa000000),

    # BL, BLX (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f000000, 0x0b000000),

    # B ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f000000, 0x0a000000),

    # BLX (Register) ARMv5TAll | ARMv6All | ARMv7
    (0x0ffffff0, 0x012fff30),

    # BX ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0x0ffffff0, 0x012fff10),

    # BXJ ARMv5TEJ, ARMv6All | ARMv7
    (0x0ffffff0, 0x012fff20),
         
    # CLZ ARMv5TAll | ARMv6All | ARMv7
    (0x0fff0ff0, 0x016f0f10),

    # CMN (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f000, 0x03700000),

    # CMN (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f010, 0x01700000),

    # CMN (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f090, 0x01700010),

    # CMP (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f000, 0x03500000),

    # CMP (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f010, 0x01500000),

    # CMP (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f090, 0x01500010),

    # DBG ARMv7 (executes as NOP in ARMv6Kand ARMv6T2),
    (0x0ffffff0, 0x0320f0f0),
            
    # EOR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x02200000),

    # EOR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x00200000),

    # EOR (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x00200010),

    # LDM/LDMIA/LDMFD (ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fd00000, 0x08900000),

    # LDMDA/LDMFA ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fd00000, 0x08100000),

    # LDMDB/LDMEA ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fd00000, 0x09100000),

    # LDMIB/LDMED ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fd00000, 0x09900000),

    # LDR (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e500000, 0x04100000),

    # LDR (literal) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f7f0000, 0x028f8000),

    # LDR (register, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e500010, 0x06100000),

    # LDRB (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e500000, 0x04500000),

    # LDRB (literal) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e5f0000, 0x045f0000),

    # LDRB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0xfe500010, 0x06500000),

    # LDRBT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f700000, 0x04700000),

    # LDRBT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f700010, 0x06700000),

    # LDREX ARMv6All | ARMv7
    (0x0ff00fff, 0x01900f9f),

    # LDREXB ARMv6K | ARMv7
    (0x0ff00fff, 0x01d00f9f),

    # LDREXD ARMv6K | ARMv7
    (0x0ff00fff, 0x01b00f9f),

    # LDREXH ARMv6K | ARMv7
    (0x0ff00fff, 0x01f00f9f),

    # LDRT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f700000, 0x04300000),

    # LDRT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f700010, 0x06300000),
            
    # LSL (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0070, 0x01a00000),

    # LSL (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef00f0, 0x01a00010),

    # LSR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0070, 0x01a00020),

    # LSR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef00f0, 0x01a00050),

    # MLA ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe000f0, 0x00200090),

    # MLS ARMv6T2 | ARMv7
    (0x0ff000f0, 0x00600090),

    # MOV (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0000, 0x03a00000),

    # MOV (immediate) ARMv6T2 | ARMv7
    (0x0ff00000, 0x03000000),

    # MOV (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0ff0, 0x01a00000),

    # MOVT ARMv6T2 | ARMv7
    (0x0ff00000, 0x03400000),

    # MUL ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe000f0, 0x00000090),

    # MVN (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0000, 0x03e00000),

    # MVN (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0010, 0x01e00000),

    # MVN (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0090, 0x01e00010),

    # NOP ARMv6K, ARMv6T2 | ARMv7
    (0x0fffffff, 0x0320f000),

    # ORR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x03800000),

    # ORR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x01800000),

    # ORR (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x01800010),

    # POP ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fff0000, 0x08bd0000),

    # POP ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fff0fff, 0x049d0004),

    # PUSH ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fff0000, 0x092d0000),

    # PUSH ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fff0fff, 0x052d0004),

    # RFE ARMv6All | ARMv7
    (0xfe50ffff, 0xf8100a00),

    # ROR (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0070, 0x01a00060),

    # ROR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef00f0, 0x01a00070),

    # RRX ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0ff0, 0x01a00060),

    # RSB (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x02600000),

    # RSB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x00600000),

    # RSB (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x00600010),
            
    # RSC (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x02e00000),

    # RSC (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x00e00000),

    # RSC (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x00e00010),

    # SBC (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x02c00000),

    # SBC (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x00c00000),

    # SBC (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x00c00010),

    # SEV ARMv6K | ARMv7 (executes as NOP in ARMv6T2),
    (0x0fffffff, 0x0320f004),

    # SMLABB, SMLABT, SMLATB, SMLATT ARMv5TEAll | ARMv6All | ARMv7
    (0x0ff00090, 0x01000080),

    # SMLALBB, SMLALBT, SMLALTB, SMLALTT ARMv5TEAll | ARMv6All | ARMv7
    (0x0ff00090, 0x01400080),

    # SMLAWB, SMLAWT ARMv5TEAll | ARMv6All | ARMv7
    (0x0ff000b0, 0x01200080),

    # SMULBB, SMULBT, SMULTB, SMULTT ARMv5TEAll | ARMv6All | ARMv7
    (0x0ff0f090, 0x01600080),

    # SMULL ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe000f0, 0x00c00090),

    # SMULWB ARMv5TEAll | ARMv6All | ARMv7
    (0x0ff0f0b0, 0x012000a0),

    # SRS ARMv6All | ARMv7
    (0xfe5fffe0, 0xf84d0500),

    # STM (STMIA, STMEA) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fd00000, 0x08800000),

    # STMDA (STMED) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fd00000, 0x08000000),

    # STMDB (STMFD) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fd00000, 0x09000000),

    # STMIB (STMFA) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fd00000, 0x09800000),

    # STR (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e500000, 0x04000000),

    # STR (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e500010, 0x06000000),

    # STRB (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e500000, 0x04400000),

    # STRB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e500010, 0x06400000),

    # STRBT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f700000, 0x04600000),

    # STRBT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f700010, 0x06600000),

    # STREX ARMv6All | ARMv7
    (0x0ff00ff0, 0x01800f90),

    # STREXB ARMv6K | ARMv7
    (0x0ff00ff0, 0x01c00f90),

    # STREXD ARMv6K | ARMv7
    (0x0ff00ff0, 0x01a00f90),

    # STREXH ARMv6K | ARMv7
    (0x0ff00ff0, 0x01e00f90),

    # STRT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f700000, 0x04200000),

    # STRT ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f700010, 0x06200000),
            
    # SUB (immediate, ARM) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00000, 0x02400000),

    # SUB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00010, 0x00400000),

    # SUB (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe00090, 0x00400010),

    # SUB (SP minus immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0000, 0x024d0000),

    # SUB (SP minus register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fef0010, 0x004d0000),

    # SUBS PC, LR and related instructions, ARM ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e10f000, 0x0210f000),

    # SUBS PC, LR and related instructions, ARM ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0e10f010, 0x0010f000),

    # SVC ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0f000000, 0x0f000000),

    # SWP, SWPB ARMv4All | ARMv5TAll | deprecated in ARMv6All and ARMv7, optional in ARMv7VE
    (0x0fb00ff0, 0x01000090),

    # TEQ (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f000, 0x03300000),

    # TEQ (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f010, 0x01300000),

    # TEQ (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f090, 0x01300010),
     
    # TST (immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f000, 0x03100000),

    # TST (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f010, 0x01100000),

    # TST (register shifted register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0ff0f090, 0x01100010),

    # UMAAL ARMv6All | ARMv7
    (0x0ff000f0, 0x00400090),

    # UMLAL ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe000f0, 0x00a00090),

    # UMULL ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0x0fe000f0, 0x00800090)
)

thumb_opcodes = \
(
    # adc (immediate) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf1400000),

    # adc (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004140),

    # adc (register) ARMv6T2 | ARMv7
    (0xffe08000, 0xeb400000),

    # ADD (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x00001c00),

    # ADD (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00003000),

    # ADD (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf1000000),

    # ADD (immediate, Thumb) ARMv6T2 | ARMv7  
    (0xfbf08000, 0xf2000000),

    # ADD (register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x00001800),

    # ADD (register, Thumb) ARMv6T2 | ARMv7
    (0xffe08000, 0xeb000000),

    # ADD (SP plus immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x0000a800),

    # ADD (SP plus immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffff80, 0x0000b000),

    # ADD (SP plus immediate) ARMv6T2 | ARMv7
    (0xfbef8000, 0xf10d0000),

    # ADD (SP plus immediate) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0xfbff8000, 0xf20d0000),

    # ADD (SP plus register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffff78, 0x00004468),

    # ADD (SP plus register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffff87, 0x00004485),

    # ADD (SP plus register, Thumb) ARMv6T2 | ARMv7
    (0xffef8000, 0xeb0d0000),

    # ADR ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x0000a000),

    # ADR ARMv6T2 | ARMv7
    (0xfbff8000, 0xf2af0000),

    # ADR ARMv6T2 | ARMv7
    (0xfbff8000, 0xf20f0000),

    # AND (immediate) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf0000000),

    # AND (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004000),

    # AND (register) ARMv6T2 | ARMv7
    (0xffe08000, 0xea000000),

    # ASR (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00001000),

    # ASR (immediate) ARMv6T2 | ARMv7
    (0xffef8030, 0xea4f0020),

    # ASR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004100),

    # ASR (register) ARMv6T2 | ARMv7
    (0xffe0f0f0, 0xfa40f000),

    # B ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff000, 0x0000d000),

    # B ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x0000e000),

    # B ARMv6T2 | ARMv7
    (0xf800d000, 0xf0008000),

    # B ARMv6T2 | ARMv7
    (0xf800d000, 0xf0009000),

    # BIC (immediate) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf0200000),

    # BIC (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004380),

    # BIC (register) ARMv6T2 | ARMv7
    (0xffe08000, 0xea200000),

    # BKPT ARMv5TAll | ARMv6All | ARMv7
    (0xffffff00, 0x0000be00),

    # BL, BLX (immediate)
    # ARMv4T | ARMv5TAll | ARMv6All | ARMv7 if J1 == J2 == 1
    (0xf800f800, 0xf000f800),

    # BL, BLX (immediate)
    # ARMv6T2 | ARMv7 otherwise
    (0xf800d000, 0xf000d000),

    # BL, BLX (immediate)
    # ARMv5TAll | ARMv6All | ARMv7 if J1 == J2 == 1
    (0xf800e800, 0xf000e800),

    # BL, BLX (immediate)
    # ARMv6T2 | ARMv7 otherwise
    (0xf800c000, 0xf000c000),
            
    # BLX (register) ARMv5TAll | ARMv6All | ARMv7
    (0xffffff87, 0x00004780),

    # BX ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffff87, 0x00004700),

    # BXJ ARMv6T2 | ARMv7
    (0xfff0ffff, 0xf3c08f00),

    # CBNZ, CBZ  ARMv6T2 | ARMv7
    (0xfffff500, 0x0000b100),
            
    # CLZ ARMv6T2 | ARMv7
    (0xfff0f0f0, 0xfab0f080),

    # CMN (immediate) ARMv6T2 | ARMv7
    (0xfbf08f00, 0xf1100f00),

    # CMN (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x000042c0),

    # CMN (register) ARMv6T2 | ARMv7
    (0xfff08f00, 0xeb100f00),

    # CMP (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00002800),

    # CMP (immediate) ARMv6T2 | ARMv7
    (0xfbf08f00, 0xf1b00f00),

    # CMP (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004280),

    # CMP (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffff00, 0x00004500),
            
    # CMP (register) ARMv6T2 | ARMv7
    (0xfff08f00, 0xebb00f00),
     
    # DBG ARMv7 (executes as NOP in ARMv6T2)
    (0xfffffff0, 0xf3af80f0),

    # EOR (immediate) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf0800000),

    # EOR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004040),

    # EOR (register) ARMv6T2 | ARMv7
    (0xffe08000, 0xea800000),

    # IT ARMv6T2 | ARMv7
    (0xffffff00, 0x0000bf00),

    # LDM/LDMIA/LDMFD (Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7 (not in ThumbEE)
    (0xfffff800, 0x0000c800),

    # LDM/LDMIA/LDMFD (Thumb) ARMv6T2 | ARMv7
    (0xffd02000, 0xe8900000),

    # LDMDB/LDMEA ARMv6T2 | ARMv7
    (0xffd00000, 0xe9100000),

    # LDR (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00006800),

    # LDR (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00009800),

    # LDR (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfff00000, 0xf8d00000),

    # LDR (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfff00800, 0xf8500800),

    # LDR (literal) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00004800),

    # LDR (literal) ARMv6T2 | ARMv7
    (0xff7f0000, 0xf85f0000),

    # LDR (register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x00005800),

    # LDR (register, Thumb) ARMv6T2 | ARMv7
    (0xfff00fc0, 0xf8500000),

    # LDRB (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00007800),

    # LDRB (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfff00000, 0xf8900000),

    # LDRB (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfff00800, 0xf8100800),

    # LDRB (literal) ARMv6T2 | ARMv7
    (0xff7f0000, 0xf81f0000),

    # LDRB (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x00005c00),

    # LDRB (register) ARMv6T2 | ARMv7
    (0xfff00fc0, 0xf8100000),

    # LDRBT ARMv6T2 | ARMv7
    (0xfff00f00, 0xf8100e00),

    # LDREX ARMv6T2 | ARMv7
    (0xfff00f00, 0xe8500f00),

    # LDREXB ARMv7
    (0xfff00fff, 0xe8d00f4f),

    # LDREXD ARMv7
    (0xfff000ff, 0xe8d0007f),

    # LDREXH ARMv7
    (0xfff00fff, 0xe8d00f5f),

    # LDRT ARMv6T2 | ARMv7
    (0xfff00f00, 0xf8500e00),

    # LSL (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00000000),

    # LSL (immediate) ARMv6T2 | ARMv7
    (0xffef8030, 0xea4f0000),

    # LSL (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004080),

    # LSL (register) ARMv6T2 | ARMv7
    (0xffe0f0f0, 0xfa00f000),

    # LSR (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00000800),

    # LSR (immediate) ARMv6T2 | ARMv7
    (0xffef8030, 0xea4f0010),

    # LSR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x000040c0),

    # LSR (register) ARMv6T2 | ARMv7
    (0xffe0f0f0, 0xfa20f000),

    # MLA ARMv6T2 | ARMv7
    (0xfff000f0, 0xfb000000),

    # MOV (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00002000),

    # MOV (immediate) ARMv6T2 | ARMv7
    (0xfbef8000, 0xf04f0000),

    # MOV (immediate) ARMv6T2 | ARMv7 
    (0xfbf08000, 0xf2400000),

    # TODO: CHECK THIS
    # MOV (register, Thumb) ARMv6All | ARMv7 if <Rd> and <Rm> both from R0-R7
    # ARMv4T | ARMv5TAll | ARMv6All | ARMv7 otherwise
    (0xffffff00, 0x00004600),

    # MOV (register, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00000000),

    # MOV (register, Thumb) ARMv6T2 | ARMv7
    (0xffeff0f0, 0xea4f0000),

    # MOVT ARMv6T2 | ARMv7
    (0xfbf08000, 0xf2c00000),

    # MUL ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004340),

    # MUL ARMv6T2 | ARMv7
    (0xfff0f0f0, 0xfb00f000),

    # MVN (immediate) ARMv6T2 | ARMv7
    (0xfbef8000, 0xf06f0000),

    # MVN (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x000043c0),

    # MVN (register) ARMv6T2 | ARMv7
    (0xffef8000, 0xea6f0000),

    # NOP ARMv6T2 | ARMv7
    (0xffffffff, 0x0000bf00),

    # NOP ARMv6T2 | ARMv7
    (0xffffffff, 0xf3af8000),

    # ORR (immediate) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf0400000),

    # ORR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004300),

    # ORR (register) ARMv6T2 | ARMv7
    (0xffe08000, 0xea400000),

    # POP (thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x0000bc00),

    # POP (thumb) ARMv6T2 | ARMv7
    (0xffff2000, 0xe8bd0000),

    # POP (thumb) ARMv6T2 | ARMv7
    (0xffff0fff, 0xf85d0b04),

    # PUSH ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x0000b400),

    # PUSH ARMv6T2 | ARMv7
    (0xffff0000, 0xe92d0000),

    # PUSH ARMv6T2 | ARMv7
    (0xffff0fff, 0xf84d0d04),

    # RFE ARMv6T2 | ARMv7
    (0xffd0ffff, 0xe810c000),

    # RFE ARMv6T2 | ARMv7
    (0xffd0ffff, 0xe990c000),

    # ROR (immediate) ARMv6T2 | ARMv7
    (0xffef8030, 0xea4f0030),

    # ROR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x000041c0),

    # ROR (register) ARMv6T2 | ARMv7
    (0xffe0f0f0, 0xfa60f000),

    # RRX ARMv6T2 | ARMv7
    (0xffeff0f0, 0xea4f0030),

    # RSB (immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004240),

    # RSB (immediate) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf1c00000),

    # RSB (register) ARMv6T2 | ARMv7
    (0xffe08000, 0xea400000),

    # SBC (immediate) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf1600000),

    # SBC (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004180),

    # SBC (register) ARMv6T2 | ARMv7
    (0xffe08000, 0xeb600000),

    # SEV ARMv7 (executes as NOP in ARMv6T2)
    (0xffffffff, 0x0000bf40),

    # SEV ARMv7 (executes as NOP in ARMv6T2)
    (0xffffffff, 0xf3af8000),

    # SMLABB, SMLABT, SMLATB, SMLATT ARMv6T2 | ARMv7
    (0xfff000c0, 0xfb100000),

    # SMLALBB, SMLALBT, SMLALTB, SMLALTT ARMv6T2 | ARMv7
    (0xfff000c0, 0xfbc00080),

    # SMLAWB, SMLAWT ARMv6T2 | ARMv7
    (0xfff000e0, 0xfb300000),

    # SMULBB, SMULBT, SMULTB, SMULTT ARMv6T2 | ARMv7
    (0xfff0f0c0, 0xfb10f000),

    # SMULL ARMv6T2 | ARMv7
    (0xfff000f0, 0xfb800000),

    # SMULWB, SMULWT ARMv6T2 | ARMv7
    (0xfff0f0e0, 0xfb30f000),

    # SRS, Thumb ARMv6T2 | ARMv7
    (0xffdfffe0, 0xe80dc000),

    # SRS, Thumb ARMv6T2 | ARMv7
    (0xffdfffe0, 0xe98dc000),

    # STM (STMIA, STMEA) ARMv4T | ARMv5TAll | ARMv6All | ARMv7 (not in ThumbEE)
    (0xfffff800, 0x0000c000),

    # STM (STMIA, STMEA) ARMv6T2 | ARMv7
    (0xffd0a000, 0xe8800000),

    # STMDB (STMFD) ARMv6T2 | ARMv7
    (0xffd00000, 0xe9000000),

    # STR (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00006000),

    # STR (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00009000),

    # STR (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfff00000, 0xf8c00000),

    # STR (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfff00800, 0xf8400800),

    # STR (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x00005000),
     
    # STR (register) ARMv6T2 | ARMv7
    (0xfff00fc0, 0xf8400000),

    # STRB (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00007000),

    # STRB (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfff00000, 0xf8800000),

    # STRB (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfff00800, 0xf8000800),

    # STRB (register) ARMv6T2 | ARMv7
    (0xfffffe00, 0x00005400),

    # STRB (register) ARMv4All | ARMv5TAll | ARMv6All | ARMv7
    (0xfff00fc0, 0xf8000000),

    # STRBT ARMv6T2 | ARMv7
    (0xfff00f00, 0xf8000e00),

    # STREX ARMv6T2 | ARMv7
    (0xfff00000, 0xe8400000),

    # STREXB ARMv7
    (0xfff00ff0, 0xe8c00f40),

    # STREXD ARMv7
    (0xfff000f0, 0xe8c00070),

    # STREXH ARMv7
    (0xfff00ff0, 0xe8c00f50),

    # STRT ARMv6T2 | ARMv7
    (0xfff00f00, 0xf8400e00),

    # SUB (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x00001e00),

    # SUB (immediate, Thumb) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffff800, 0x00003800),

    # SUB (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfbe08000, 0xf1a00000),

    # SUB (immediate, Thumb) ARMv6T2 | ARMv7
    (0xfbf08000, 0xf2a00000),

    # SUB (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xfffffe00, 0x00001a00),

    # SUB (register) ARMv6T2 | ARMv7
    (0xffe08000, 0xeba00000),

    # SUB (SP minus immediate) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffff80, 0x0000b080),

    # SUB (SP minus immediate) ARMv6T2 | ARMv7
    (0xfbef8000, 0xf1ad0000),

    # SUB (SP minus immediate) ARMv6T2 | ARMv7
    (0xfbff8000, 0xf2ad0000),

    # SUB (SP minus register) ARMv6T2 | ARMv7
    (0xffef8000, 0xebad0000),

    # SUBS PC, LR, Thumb ARMv6T2 | ARMv7
    (0xffffff00, 0xf3de8f00),

    # SVC (previously SWI) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffff00, 0x0000df00),

    # TEQ (immediate) ARMv6T2 | ARMv7
    (0xfbf08f00, 0xf0900f00),

    # TEQ (register) ARMv6T2 | ARMv7
    (0xfff08f00, 0xea900f00),

    # TST (immediate) ARMv6T2 | ARMv7
    (0xfbf08f00, 0xf0100f00),

    # TST (register) ARMv4T | ARMv5TAll | ARMv6All | ARMv7
    (0xffffffc0, 0x00004200),

    # TST (register) ARMv6T2 | ARMv7
    (0xfff08f00, 0xea100f00),

    # UMAAL ARMv6T2 | ARMv7
    (0xfff000f0, 0xfbe00060),

    # UMLAL ARMv6T2 | ARMv7
    (0xfff000f0, 0xfbe00000),

    # MULL ARMv6T2 | ARMv7
    (0xfff000f0, 0xfba00000),

    # WFE ARMv7 (executes as NOP in ARMv6T2)
    (0xffffffff, 0x0000bf20),

    # WFE ARMv7 (executes as NOP in ARMv6T2)
    (0xffffffff, 0xf3af8002),

    # WFI ARMv7 (executes as NOP in ARMv6T2)
    (0xffffffff, 0x0000bf30),

    # WFI ARMv7 (executes as NOP in ARMv6T2)
    (0xffffffff, 0xf3af8003),

    # YIELD ARMv7 (executes as NOP in ARMv6T2)
    (0xffffffff, 0x0000bf10),

    # YIELD ARMv7 (executes as NOP in ARMv6T2)
    (0xffffffff, 0xf3af8001),
)


def tets_emulator(mask, value, mode, limit=1000):
    seen = set()
    
    d = ARMDisassembler()
    
    for i in xrange(limit):
        opcode = get_masked_random(mask, value, mode)

        if opcode in seen:
            continue
        
        seen.add(opcode)
        
        if (opcode & mask) != value:
            continue
        
        opcode = opcode | 0xe0000000
        
        try:
            memory_map = DummyMemoryMap()
            emulator = ARMEmulator(memory_map)                        
            inst = d.disassemble(opcode, mode=mode)
            emulator.emulate(inst, True)
            emulator.setCurrentMode(ARMMode.ARM)
        
        except NotImplementedError:
            continue
        
        except UnpredictableInstructionException:
            continue
        
        except InstructionNotImplementedException:
            continue
        
        except RuntimeError:
            continue

def test(mask, value, mode, limit=10000):
    seen = set()
    
    d = ARMDisassembler()
    
    ok = 0
    bad = 0
    not_implemented = 0
    unpredictable = 0
    skipped = 0
    invalid_encoding = 0
    undefined = 0
    
    for i in xrange(limit):
        opcode = get_masked_random(mask, value, mode)
        
        if opcode in seen:
            continue
        
        seen.add(opcode)
        
        if (opcode & mask) != value:
            continue

        try:
            if mode == ARMMode.THUMB:
                llvm_out = llvm.disassemble(opcode, mode=ARMMode.THUMB).lower()
                inst_theirs = objdump.disassemble(opcode, mode=ARMMode.THUMB).lower().replace(".n", "")
            else:
                llvm_out = llvm.disassemble(opcode, mode=ARMMode.ARM).lower()
                inst_theirs = objdump.disassemble(opcode, mode=ARMMode.ARM).lower().replace(".n", "")

            inst = d.disassemble(opcode, mode=mode)
            if not inst:
                print "# inst == None"
                print "# OBJD: ", inst_theirs
                print "# LLVM: ", llvm_out
                print "opcode = 0x%.8x" % opcode 
                print
                
                skipped += 1
                continue
            
            inst_ours = str(inst).lower()
            
            our_oprand = inst_ours.split(" ")[0]
            their_oprand = llvm_out.split(" ")[0]
            objdump_oprand = inst_theirs.split(" ")[0]
            our_args = inst_ours.split(" ")[1:]
            their_args = llvm_out.split(" ")[1:]
            
            if our_oprand != their_oprand:
                if our_oprand[-2:] == "cs" and their_oprand[-2:] == "hs":
                    ok += 1
                    continue
                
                elif our_oprand[-2:] == "cc" and their_oprand[-2:] == "lo":
                    ok += 1
                    continue
                
                # TODO: These cases should be fixed on our side
                if their_oprand == "invalid":
                    ok += 1
                    continue

                if their_oprand == "undefined":
                    ok += 1
                    
                    # Sometimes LLVM fails
                    if our_oprand == objdump_oprand:
                        continue    
                    
                    print "# OURS: ", inst_ours
                    print "# OBJD: ", inst_theirs
                    print "# LLVM: ", llvm_out
                    print "opcode = 0x%.8x" % opcode 
                    print

                    continue
                
                bad += 1
                
                print "# OPERAND Difference"
                print "# OURS: ", inst_ours
                print "# OBJD: ", inst_theirs
                print "# LLVM: ", llvm_out
                print "opcode = 0x%.8x" % opcode 
                print
                
            elif "".join(our_args) != "".join(their_args):
                bad += 1
                
                print "# ARGUMENT Difference"
                print "# OURS: ", inst_ours
                print "# OBJD: ", inst_theirs
                print "# LLVM: ", llvm_out
                print "opcode = 0x%.8x" % opcode 
                print
                
            else:
                ok += 1
                print "# OK OK OK"
                print "# OURS: ", inst_ours
                print "# OBJD: ", inst_theirs
                print "# LLVM: ", llvm_out
                print "opcode = 0x%.8x" % opcode 
                print

        except InstructionNotImplementedException, e:
            not_implemented += 1
            continue
        
            print "# O: ", "NotImplemented", e
            print "# OBJD: ", inst_theirs
            print "# LLVM: ", llvm_out
            print "opcode = 0x%.8x" % opcode 
            print
                                
        except UnpredictableInstructionException, e:
            if llvm_out == "undefined":
                ok += 1
                continue
            
            continue
            
            unpredictable += 1
            print "# O: ", "Unpredictable", e
            print "# OBJD: ", inst_theirs
            print "# LLVM: ", llvm_out
            print "opcode = 0x%.8x" % opcode 
            print
            
        except InvalidInstructionEncoding, e:
            invalid_encoding += 1
            
            if llvm_out == "undefined":
                continue
            
            print "# O: ", "Invalid encoding", e
            print "# OBJD: ", inst_theirs
            print "# LLVM: ", llvm_out
            print "opcode = 0x%.8x" % opcode 
            print
            
        except UndefinedOpcode, e:
            undefined += 1
            if llvm_out == "undefined":
                continue
            
            print "# O: ", "Undefined", e
            print "# OBJD: ", inst_theirs
            print "# LLVM: ", llvm_out
            print "opcode = 0x%.8x" % opcode 
            print
        
    print "# Tested %d instructions" % limit
    print "#   OK             : %d" % ok
    print "#   BAD            : %d" % bad
    print "#   Unpredictable  : %d" % unpredictable
    print "#   NotImplemented : %d" % not_implemented
    print "#   Skipped        : %d" % skipped
    print "#   InvalidEncoding: %d" % invalid_encoding
    print "#   Undefined: %d" % undefined
            
    return 0

from disassembler.constants.arm import ARMMode

def main():
#     for i in xrange(0, len(arm_opcodes)):
#         print "=" * 80
#         print "INDEX: %d" % i
#         mask, value = arm_opcodes[i]
#         test(mask, value, ARMMode.THUMB, limit=100)

#     mask, value = (0xfffffe00, 0x00001800)
#     test(mask, value, ARMMode.THUMB, limit=10)
#     return

#     for i in xrange(0, len(thumb_opcodes)):
#     #i = 18
#     #for i in xrange(i, i+1):
#         print "# " + ("=" * 80)
#         print "# INDEX: %d" % i        
#         mask, value = thumb_opcodes[i]
#         test(mask, value, ARMMode.THUMB, limit=500)
    
#    mask, value = (0x0fe00000, 0x02a00000)
#     test(mask, value, ARMMode.ARM, limit=100)

    for i in xrange(0, len(arm_opcodes)):
        print "=" * 80
        print "INDEX: %d" % i
        mask, value = arm_opcodes[i]    
        tets_emulator(mask, value, ARMMode.ARM, limit=1000)
    
if __name__ == "__main__":
    main()
