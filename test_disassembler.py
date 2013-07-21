from disassembler.arm import ARMDisassembler
from disassembler.constants.arm import ARMMode

def main():
    d = ARMDisassembler()
    # OURS:  ldrb r7, [r6, #120]
    # OBJD:  ldrb r7, [r6, #30]
    # LLVM:  ldrb r7, [r6, #30]
    opcode = 0x00007fb7
    
    inst = d.disassemble(opcode, mode=ARMMode.THUMB)
    print inst

if __name__ == "__main__":
    main()
