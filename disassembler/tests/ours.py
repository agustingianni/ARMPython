import sys
sys.path.append("../../")
sys.path.append(".")

from disassembler.arm import ARMDisassembler
from disassembler.constants.arm import ARMMode

__author__ = 'anon'

# argv[1] == 1 -> ARM
# argv[1] == 2 -> THUMB
if __name__ == "__main__":
    if int(sys.argv[1]) == 1:
        mode = ARMMode.ARM
    else:
        mode = ARMMode.THUMB

    arm_dis = ARMDisassembler()
    print arm_dis.disassemble(int(sys.argv[2], 16), mode)
