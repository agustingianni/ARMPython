import argparse
import sys

from disassembler.arm import ARMDisassembler
from disassembler.arch import ARMMode
import struct
import binascii

def main():
    parser = argparse.ArgumentParser()    
    parser.add_argument("data", help="The data you want to disassemble (example: \"e0909090\").")
    parser.add_argument("-a", "--arm", help="Dissasemble data as ARM", action="store_true")
    parser.add_argument("-t", "--thumb", help="Dissasemble data as THUMB", action="store_true")
    
    args = parser.parse_args()
    if args.thumb:
        print "Using THUMB mode"
        mode = ARMMode.THUMB
        
    elif args.arm:
        print "Using ARM mode"
        mode = ARMMode.ARM
        
    else:
        print "Defaulting to THUMB mode"
        mode = ARMMode.THUMB
        
    if "0x" in args.data.lower():
        try:
            data = struct.pack("<L", int(args.data, 16))
            
        except ValueError:
            print "Invalid input opcode %s" % (args.data)
            sys.exit(-1)
    else:
        data = binascii.unhexlify(args.data)
    
    print "Disassembling %s" % (binascii.hexlify(data))
    
    d = ARMDisassembler()

    instructions = d.disassemble_buffer(data, mode)
    for ins in instructions:
        print ins

if __name__ == "__main__":
    main()
