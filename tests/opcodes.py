'''
Created on Jun 7, 2013

@author: anon
'''
import fnmatch
import os
import arm
from subprocess import check_output
from objdump import disassemble

assembler = "arm-linux-androideabi-as"
disassembler = "arm-linux-androideabi-objdump"

def disassemble_mc(opcode):
    output = check_output(["/usr/lib/llvm-3.0/bin/llvm-mc", "--disassemble", "-triple=armv7"])


def test2():
# ins nro: 45105
# O:  str pc, [lr, #-2905]
# T:  
    opcode = 0xf50efb59
    d = arm.ARMDisasembler()
    inst = d.disassemble(opcode, mode=arm.MODE_ARM)
    inst_theirs = disassemble(opcode, whole=True).lower()
    inst_ours = str(inst).lower()
    
    print inst_theirs
    print inst_ours

#test2()
#sys.exit()

def test():
    d = arm.ARMDisasembler()
    i = 0
    
    ok = 0
    bad = 0
    for file_ in os.listdir('.'):
        if fnmatch.fnmatch(file_, 'arm_opcodes.txt'):
            print "Testing file %s" % file_
            
            for line in open(file_):
                m, o, b = line.split("|")
                b = int(b, 16)
                                
                try:
                    inst = d.disassemble(b, mode=arm.MODE_ARM)
                    if not inst:
                        continue
                    
                    i += 1
                    inst_theirs = disassemble(b).lower().replace(".n", "")
                    inst_ours = str(inst).lower()
                    
                    if inst_ours.split(" ")[0] != inst_theirs.split(" ")[0]:                        
                        # Skip stupid objdump mixup
                        if inst_ours.split(" ")[0].startswith("stm") and inst_theirs.split(" ")[0].startswith("stm"):
                            continue
                                                
                        # We do not implement this yet.
                        if "strh" in inst_theirs:
                            continue

                        if "ldrh" in inst_theirs:
                            continue

                        if "neg" in inst_theirs:
                            continue
                        
                        # IDA is weird, it seems like it defaults everything to BL
                        if "BL" in o:
                            continue
                        
                        bad += 1
                        continue
                        #if "sbc" in inst_ours:
                        #    continue
                        #
                        #if "svc" in inst_ours:
                        #    continue
                    
                        print "# ins nro: %d" % i
                        print "# O: ", inst_ours
                        print "# T: ", inst_theirs
                        print "# I: ", o
                        print "opcode = 0x%.8x" % b 
                        print
                         
                    else:
                        ok += 1
                        
                except arm.InstructionNotImplementedException, e:
                    continue
                
                    print "# ins nro: %d" % i
                    print "# O: ", "NotImplemented"
                    print "# T: ", inst_theirs
                    print "# I: ", o
                    print "opcode = 0x%.8x" % b
                    print 
                                        
                except arm.UnpredictableInstructionException, e:
                    continue
                    print "# ins nro: %d" % i
                    print "# O: ", "Unpredictable"
                    print "# T: ", inst_theirs
                    print "# I: ", o
                    print "opcode = 0x%.8x" % b 
                    print                 
                 
    print "OK  ", ok
    print "BAD ", bad

if __name__ == '__main__':
    test()