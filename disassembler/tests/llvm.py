'''
Created on Jun 11, 2013

@author: anon
'''
import struct
import binascii

from subprocess import Popen, PIPE, STDOUT
from itertools import izip

disassembler = "llvm-mc"

def pairwise(iterable):
    a = iter(iterable)
    return izip(a, a)

def disassemble(opcode, mode=0, whole=False):
    tmp = ""
    
    if mode == 1:
        for a, b in pairwise(list(binascii.b2a_hex(struct.pack("<L", opcode)))):
            tmp += "0x%c%c " % (a, b) 
            
    else:
        if opcode & 0xffff0000:
            fmt = "<L"
        else:
            fmt = "<H"
            
        for a, b in pairwise(list(binascii.b2a_hex(struct.pack(fmt, opcode)))):
            tmp += "0x%c%c " % (a, b) 
                
    if mode == 1:
        p = Popen([disassembler, '-disassemble', '-arch=arm'], stdout=PIPE, stdin=PIPE, stderr=STDOUT)
        
    else:
        p = Popen([disassembler, '-disassemble', '-arch=thumb'], stdout=PIPE, stdin=PIPE, stderr=STDOUT)
        
    out = p.communicate(input=tmp)[0]

    if not whole:
        out = out.strip()
        out = out.replace("\t", " ")
        out = out.replace("r12", "ip")
        out = out.replace("r11", "fp")
        out = out.replace("r10", "sl")
        out = out.split("\n")[1].strip()

        if "undefined" in out:
            out = "Undefined"

        if "invalid" in out:
            out = "Undefined"
        
    return out

import sys
# argv[1] == 1 -> ARM
# argv[1] == 2 -> THUMB
if __name__ == "__main__":
    print disassemble(int(sys.argv[2], 16), int(sys.argv[1]), whole=True)