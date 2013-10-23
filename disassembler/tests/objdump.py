'''
Created on Jun 11, 2013

@author: anon
'''
import struct
from subprocess import check_output

disassembler = "arm-linux-androideabi-objdump"

def disassemble(opcode, mode=0, whole=False):
    f = open("test.o", "w")
    f.write(struct.pack("<L", opcode))
    f.close()
    
    if mode == 1:
        output = check_output([disassembler, "-D", "-b", "binary", "-marm", "test.o"])
    else:
        output = check_output([disassembler, "-D", "-b", "binary", "-marm", "-Mforce-thumb", "test.o"])
    
    if whole:
        print output
        return
    
    res = []
    for line in output.split("\n"):
        t = line.split()
        if not len(t) or not ("0:" in t):
            continue
        
        op = int(t[1], 16)
        
        if "UNDEFINED" in line:
            return "Undefined"
        
        # dis = t[2:]
        if not (';' in t[2:]):
            dis = t[2:]
        else:
            # Drop the comment in a really ghetto way
            idx = t[2:].index(";")
            dis = t[2:2 + idx]
        
        return " ".join(dis)

    return ""

import sys
# argv[1] == 1 -> ARM
# argv[1] == 2 -> THUMB
if __name__ == "__main__":
    print disassemble(int(sys.argv[2], 16), int(sys.argv[1]))