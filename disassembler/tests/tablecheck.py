'''
Created on Jun 11, 2013

@author: anon
'''
import sys
sys.path.append("../../")

from emulator.ARMEmulator import ARMEmulator
from emulator.memory import DummyMemoryMap

from disassembler.arm import ARMDisassembler
from disassembler.arch import UndefinedOpcode, InvalidInstructionEncoding
from disassembler.arch import UnpredictableInstructionException, InstructionNotImplementedException
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

def tets_emulator(mask, value, mode, limit=1000):
    seen = set()
    
    d = ARMDisassembler()
    
    for i in xrange(limit):
        opcode = get_masked_random(mask, value, mode) & 0xefffffff

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
    
    # Inacurate hack.
    is_thumb32 = value > 0xffff and mode == ARMMode.THUMB
        
    for i in xrange(limit):
        opcode = get_masked_random(mask, value, mode)
        if not is_thumb32 and (value & 0xf0000000) != 0xf0000000:
            opcode &= 0xefffffff
        
        if opcode in seen:
            continue
    
        if (opcode & mask) != value:
            print "%.8x != %.8x, opcode = %.8x" % (opcode & mask, value, opcode)
            continue
        
        seen.add(opcode)

        # When testing THUMB32 we need to do this. Sucks.
        if is_thumb32:
            opcode = ((opcode & 0xffff0000) >> 16) | ((opcode & 0x0000ffff) << 16)
        
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
            
            # The case where llvm_out is '0x79 0xf7 0x9d 0xf5'
            if llvm_out[0] == "0":
                llvm_out = inst_theirs
            
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
                continue
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
            
        except RuntimeError, e:
            print "RUNTIME: %s" % e
            continue
        
    print "# Tested %d instructions" % limit
    print "#   OK             : %d" % ok
    print "#   BAD            : %d" % bad
    print "#   Unpredictable  : %d" % unpredictable
    print "#   NotImplemented : %d" % not_implemented
    print "#   Skipped        : %d" % skipped
    print "#   InvalidEncoding: %d" % invalid_encoding
    print "#   Undefined: %d" % undefined
            
    return 0

def test_decoding():
    d = ARMDisassembler()
        
    thumb_table = d.thumb_table
    arm_table = d.arm_table

    d.disassemble(0xf3af8000, ARMMode.THUMB)

    # VMOV Advanced SIMD
    # (0xfeb80090, 0xf2800010, SIMD, eEncodingA1, No_VFP, eSize32, self.decode_vmov_immediate),
    # VMOV Advanced SIMD
    # (0x0fb00ef0, 0x0eb00a00, SIMD, eEncodingA2, No_VFP, eSize32, self.decode_vmov_immediate),

        
    arm_table = [(0xfeb80090, 0xf2800010), (0x0fb00ef0, 0x0eb00a00)]
    thumb_table = []

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
        
        #break
   
if __name__ == "__main__":
    test_decoding()
