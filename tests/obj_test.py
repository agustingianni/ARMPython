'''
Created on Dec 10, 2012

@author: agustin
'''

import sys
from arm import ARMDisasembler
from arm import UnpredictableInstructionException
from arm import InstructionNotImplementedException
from subprocess import check_output
from collections import defaultdict

assembler = "arm-linux-androideabi-as"
disassembler = "arm-linux-androideabi-objdump"

def assemble():
    output = check_output([assembler, "-o", "test.o", "test.s"])
    return output

def disassemble(file):
    output = check_output([disassembler, "-D", file])
    res = []
    for line in output.split("\n"):
        if ".word" in line:
            continue

        if ".short" in line:
            continue

        if ".byte" in line:
            continue
        
        if "UNDEFINED" in line:
            continue 

        t = line.split()
        if not len(t) or len(t) < 2:
            continue
                
        try:
            op = int(t[1], 16)
            dis = t[2:]
        except ValueError:
            continue
                
        res.append((op, " ".join(dis).split(";")[0]))

    return res

def test():
    freq = defaultdict(int)
    
    arm_dis = ARMDisasembler()
    for ins in disassemble(sys.argv[1]):
        opcode = ins[1].split()[0]
        freq[opcode] += 1
        
    for key, value in sorted(freq.iteritems(), key=lambda (k,v): (v,k), reverse=True):
        print "%s: %s" % (key, value)

if __name__ == '__main__':
    test()