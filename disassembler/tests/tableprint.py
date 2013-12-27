'''
Created on Jun 11, 2013

@author: anon
'''
import sys
sys.path.append("../../")

from disassembler.arm import ARMDisassembler
from disassembler.arch import UndefinedOpcode
from disassembler.arch import UnpredictableInstructionException
from disassembler.arch import ARMMode

import random
import objdump
import llvm

def get_masked_random(mask, value, mode=1):
    r = random.getrandbits(32)
    
    for i in xrange(0, 32):
        if mask & (1 << i):
            if value & (1 << i):
                r |= value & (1 << i)
            else:
                r &= ~(1 << i)
    
    return r

def test(mask, value, mode, limit=10000):
    seen = set()
    
    d = ARMDisassembler()
        
    # Inacurate hack.
    is_thumb32 = value > 0xffff and mode == ARMMode.THUMB
        
    for i in xrange(limit):
        opcode = get_masked_random(mask, value, mode)
        if not is_thumb32 and (value & 0xf0000000) != 0xf0000000:
            opcode &= 0xefffffff
        
        if opcode in seen:
            continue
    
        if (opcode & mask) != value:
            continue
        
        seen.add(opcode)

        # When testing THUMB32 we need to do this. Sucks.
        if is_thumb32:
            opcode = ((opcode & 0xffff0000) >> 16) | ((opcode & 0x0000ffff) << 16)
        
        if mode == ARMMode.THUMB:
            llvm_out = llvm.disassemble(opcode, mode=ARMMode.THUMB).lower()
            inst_theirs = objdump.disassemble(opcode, mode=ARMMode.THUMB).lower().replace(".n", "")

        else:
            llvm_out = llvm.disassemble(opcode, mode=ARMMode.ARM).lower()
            inst_theirs = objdump.disassemble(opcode, mode=ARMMode.ARM).lower().replace(".n", "")

        try:
            inst_ours = d.disassemble(opcode, mode=mode)
        
        except RuntimeError, e:
            inst_ours = str(e)
        
        except UndefinedOpcode:
            inst_ours = "UNDEFINED"

        except UnpredictableInstructionException:
            inst_ours = "UNPREDICTABLE"

        import darm

        # if str(inst_ours).lower() == inst_theirs.lower():
        #    continue
        
        print "# OURS: ", str(inst_ours).lower()
        print "# OBJD: ", inst_theirs.lower()
        print "# LLVM: ", llvm_out.lower()
        print "# DARM: ", str(darm.disasm_armv7(opcode))
        print "opcode = 0x%.8x" % opcode 
        print
                    
    return 0

def test_decoding():
    # Get the tables.
    d = ARMDisassembler()        
    thumb_table = d.thumb_table
    arm_table = d.arm_table
        
    thumb_table = [ \
        (0xfff08020, 0xf3600000),
        (0xff000010, 0xee000000),
        (0xff000010, 0xfe000000),
        (0xffffffff, 0xf3bf8f2f),
        (0xffffffe8, 0x0000b660),
        (0xfffff800, 0xf3af8000),
        (0xfffffff0, 0xf3bf8f50),
        (0xfffffff0, 0xf3bf8f40),
        (0xffffff00, 0xf3bf8f00),
        (0xfff0f000, 0xf7e08000),
        (0xfffffff0, 0xf3bf8f60),
        (0xfe100000, 0xec100000),
        (0xfffffff0, 0xfc100000),
        (0xfe1f0000, 0xec1f0000),
        (0xfe1f0000, 0xfc1f0000),
        (0xfe500000, 0xe8500000),
        (0xfe5f0000, 0xe85f0000),
        (0xff7f0000, 0xf83f0000),
        (0xfffffe00, 0x00005a00),
        (0xfff00fc0, 0xf8300000),
        (0xfff00f00, 0xf8300e00),
        (0xfff00000, 0xf9900000),
        (0xfff00800, 0xf9100800),
        (0xff7f0000, 0xf91f0000),
        (0xfffffe00, 0x00005600),
        (0xfff00fc0, 0xf9100000),
        (0xfff00f00, 0xf9100f00),
        (0xfff00000, 0xf9b00000),
        (0xfff00800, 0xf9300800),
        (0xff7f0000, 0xf93f0000),
        (0xfffffe00, 0x00005e00),
        (0xfff00fc0, 0xf9300000),
        (0xfff00f00, 0xf9300e00)]
    
    thumb_table = []
    
    arm_table   = [ \
        (0x0f300f00, 0x0d000a00),                            
        (0x0fe00f7f, 0x0e000a10),
        (0x0f300f00, 0x0d100a00),                   
        (0x0e100000, 0x0c100000),
        (0xfffffff0, 0xfc100000),        
        ]

    print "Testing THUMB Decoding"
    for i in xrange(0, len(thumb_table)):
        mask, value = thumb_table[i][0], thumb_table[i][1]

        print "=" * 80
        print "INDEX: %d" % i
        print "MASK %.8x | VALUE %.8x" % (mask, value)
        print "Instruction: ", thumb_table[i][-1]
        test(mask, value, ARMMode.THUMB, limit=100)
        
    
    print "Testing ARM Decoding"
    for i in xrange(0, len(arm_table)):
        mask, value = arm_table[i][0], arm_table[i][1]

        print "=" * 80
        print "INDEX: %d" % i
        print "MASK %.8x | VALUE %.8x" % (mask, value)
        print "Instruction: ", arm_table[i][-1]
        test(mask, value, ARMMode.ARM, limit=1000)
        
        break
        
if __name__ == "__main__":
    test_decoding()
