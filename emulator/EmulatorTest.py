from emulator.memory import DummyMemoryMap
from ARMEmulator import ARMEmulator
from arm import Immediate, Instruction, Register, RegisterShift
from constants.arm import ARMRegister, ARMInstruction, eEncodingA1, eEncodingA2, SRType_ASR

memory_map = DummyMemoryMap() 
emulator = ARMEmulator(memory_map)

ins = Instruction("ADC", True, None, [Register(ARMRegister.R0), Register(ARMRegister.R1), Immediate(100)], eEncodingA1)
ins.id = ARMInstruction.adc_immediate
emulator.emulate(ins, dump_state=True)

ins = Instruction("ADC", True, None, [Register(ARMRegister.R0), Register(ARMRegister.R0)], eEncodingA1)
ins.id = ARMInstruction.adc_register
emulator.emulate(ins, dump_state=True)
 
ins = Instruction("ADC", True, None, [Register(ARMRegister.R0), Register(ARMRegister.R0), Register(ARMRegister.R2), RegisterShift(SRType_ASR, 4)], eEncodingA2)
ins.id = ARMInstruction.adc_rsr
emulator.emulate(ins, dump_state=True)
