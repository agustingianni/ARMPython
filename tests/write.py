import sys
import struct
opcode = int(sys.argv[1], 16)
f = open("test.o", "w")
f.write(struct.pack("<L", opcode))
f.close()

