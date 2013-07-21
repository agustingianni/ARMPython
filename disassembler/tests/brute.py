import sys
sys.path.append("../../")

from disassembler.arm import ARMDisassembler
from subprocess import check_output
from disassembler.arm import UnpredictableInstructionException
from disassembler.arm import InstructionNotImplementedException

assembler = "arm-linux-androideabi-as"
disassembler = "arm-linux-androideabi-objdump"

def assemble(file):
    output = check_output([assembler, "-o", "test.o", file])
    return output

def disassemble():
    output = check_output([disassembler, "-d", "test.o"])
    res = []
    for line in output.split("\n"):
        t = line.split()
        if not len(t):
            continue        
        
        try:
            op = int(t[1], 16)
        except:
            continue
        
        if not (';' in t[2:]):
            dis = t[2:]
        else:
            # Drop the comment in a really ghetto way
            idx = t[2:].index(";")
            dis = t[2:2+idx]
        
        if " ".join(dis) == '':
            continue
        
        #print (op, " ".join(dis))
        
        res.append((op, " ".join(dis), line))

    return res

def validate(arm_dis, res, show=False):
    for r in res:
        try:
            o = arm_dis.disassemble(r[0])
            if not o:
#                 print "  ins == NULL"
#                 print "  OPCode  : %.8x" % r[0] 
#                 print "  objdump :", map(lambda x: x.lower(), r[1].split())  
                #raise Exception("Our disassembler returned null")
                continue
            
            if set(map(lambda x: x.lower(), r[1].split())) != set(map(lambda x: x.lower(), o.split())):
                t = o.split()
                if t[-2] == "lsl" and t[-1] == "#0":
                    continue

                if "UNPREDICTABLE" in r[1]:
                    # Should not appear
                    print "Unpredictable"
                    continue
                            
#                 print "Difference!:"
#                 print "  OPCode  : %.8x" % r[0] 
#                 print "  objdump :", map(lambda x: x.lower(), r[1].split())  
#                 print "  ours    :", map(lambda x: x.lower(), o.split())
                
            elif show:
                print "Match!:"
                print "  OPCode  : %.8x" % r[0] 
                print "  objdump :", map(lambda x: x.lower(), r[1].split())  
                print "  ours    :", map(lambda x: x.lower(), o.split())
                    
        except UnpredictableInstructionException:
            #print "Unpredictable"
            continue
        
        except InstructionNotImplementedException, e:
            print "Not Implemented"
            print "  OPCode  : %.8x" % r[0] 
            print "  objdump :", map(lambda x: x.lower(), r[1].split())
            print e
            
            continue


f = open("test.s", "w")
for i in xrange(0xfffff, 0xffffff):
    f.write(".word 0x%.8x\n" % (i))

f.close()
assemble("test.s")    

arm_dis = ARMDisassembler()
# res is an array of instructions

res = disassemble()
validate(arm_dis, res, False)
