from emulator.ARMEmulator import ARMEmulator
from emulator.memory import ConcreteMemoryMap, MemoryMap
import logging

def main():
    logging.basicConfig(level=logging.INFO)

    # Build a concrete memory map.
    memory_map = ConcreteMemoryMap()

    # Fill the memory map with instructions at memory address 0xcafe0000
    ins = "\x00\x00\xa0\xe3\x01\x10\xa0\xe3\x02\x20\xa0\xe3\x03\x30\xa0\xe3\x04\x40\xa0\xe3\x05\x50\xa0\xe3\x06\x60\xa0\xe3\x07\x70\xa0\xe3\x08\x80\xa0\xe3\x09\x90\xa0\xe3\x01\x00\x80\xe2\x01\x10\x81\xe2\x01\x20\x82\xe2\x01\x30\x83\xe2\x01\x40\x84\xe2\x01\x50\x85\xe2\x01\x60\x86\xe2\x01\x70\x87\xe2\x01\x80\x88\xe2\x01\x90\x89\xe2"
    memory_map.set_bytes(0xcafe0000, ins)
    
    emulator = ARMEmulator(memory_map)
    emulator.setPC(0xcafe0000)
    
    # Step some of them.
    emulator.step()
    emulator.step()
    emulator.step()
    
    memory_map.set_dword(0xcafecafe, 0xdeadcafe)
    print "%x" % memory_map.get_dword(0xcafecafe)
    memory_map.setMode(MemoryMap.BigEndianMode)
    print "%x" % memory_map.get_dword(0xcafecafe)

if __name__ == '__main__':
    main()
