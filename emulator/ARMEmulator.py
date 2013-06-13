"""
Created on Jun 12, 2013

@author: anon
"""

import logging
from constants.arm import *

from arm import InstructionNotImplementedException, ARMv7, \
    UnpredictableInstructionException, InvalidModeException, Instruction, \
    eEncodingA1, Immediate, Register, eEncodingT1, RegisterShift

from emulator.memory import DummyMemoryMap
from bits import get_bits, get_bit, SignExtend32, SignExtend64

def AddWithCarry(x, y, carry_in):
    from ctypes import c_uint32, c_int32

    # unsigned_sum = UInt(x) + UInt(y) + UInt(carry_in);
    unsigned_sum = c_uint32(x).value + c_uint32(y).value + c_uint32(carry_in).value
    
    # = SInt(x) + SInt(y) + UInt(carry_in);
    signed_sum = c_int32(x).value + c_int32(y).value + c_uint32(carry_in).value

    # result = unsigned_sum<N-1:0>;
    result = get_bits(unsigned_sum, 31, 0)
    
    # carry_out = if UInt(result) == unsigned_sum then '0' else '1';
    if c_uint32(result).value == signed_sum:
        carry_out = 0
    else:
        carry_out = 1
    
    # overflow = if SInt(result) == signed_sum then '0' else '1'; 
    if c_int32(result).value == signed_sum:
        overflow = 0
    else:
        overflow = 1
        
    return result, carry_out, overflow 

def LSL_C(value, amount):
    if amount <= 0:
        raise Exception("amount <= 0")
    
    result = value << amount
    if get_bit(result, 32):
        carry_out = 1
    else:
        carry_out = 0
    
    # Make the result 32 bit
    result &= 0xffffffff
    return (result, carry_out)

def LSL(value, amount):
    if amount < 0:
        raise Exception("amount < 0")

    if amount == 0:
        result = value
    else:
        result, carry_out = LSL_C(value, amount)
        
    return result

def LSR_C(value, amount):
    if amount <= 0:
        raise Exception("amount <= 0")    
    
    result = value >> amount
    if get_bit(result, amount - 1):
        carry_out = 1
    else:
        carry_out = 0
    
    # Make the result 32 bit
    result &= 0xffffffff
    return (result, carry_out)

def LSR(value, amount):
    if amount < 0:
        raise Exception("amount < 0")
    
    if amount == 0:
        result = value
    else:
        result, carry_out = LSR_C(value, amount)
        
    return result

def ASR_C(value, amount):
    if amount <= 0:
        raise Exception("amount <= 0")
    
    if amount <= 32:
        carry_out = get_bit(value, amount - 1)
        extended = SignExtend64(value, 32)
        value = get_bits(extended, amount + 31, amount)
    else:
        if get_bit(value, 31):
            carry_out = 1
            value = 0xffffffff
        else:
            carry_out = 0
            value = 0
            
    return (value, carry_out)

def ASR(value, amount):
    if amount < 0:
        raise Exception("amount < 0")
    
    if amount == 0:
        return value
    else:
        result, carry_out = ASR_C(value, amount)
        return result

def Rotr32(bits, amt):
    return (bits >> amt) | (bits << ((32 - amt) & 31))
    
def ROR_C(value, amount):
    amt = amount % 32
    result = Rotr32(value, amt)
    carry_out = get_bit(value, 31)
    return (result, carry_out)

def ROR(value, amount):
    if amount == 0:
        return value
    else:
        result, carry_out = ROR_C(value, amount)
        return result
    
def RRX_C(value, carry_in):
    carry_out = get_bit(value, 0)
    return (((get_bit(carry_in, 0) << 31) | get_bits(value, 31, 1)), carry_out)

def RRX(value, carry_in):
    result, carry_out = RRX_C(value, carry_in)
    return result

def Shift_C(value, type_, amount, carry_in):
    if amount == 0:
        carry_out = carry_in
        return (value, carry_out)
    
    if type_ == SRType_LSL:
        result, carry_out = LSL_C(value, amount)
    
    elif type_ == SRType_LSR:
        result, carry_out = LSR_C(value, amount)
    
    elif type_ == SRType_ASR:
        result, carry_out = ASR_C(value, amount)
    
    elif type_ == SRType_ROR:
        result, carry_out = ROR_C(value, amount)
    
    elif type_ == SRType_RRX:
        result, carry_out = RRX_C(value, amount)
        
    return (result, carry_out)

def Shift(value, type_, amount, carry_in):
    result, carry_out = Shift_C(value, type_, amount, carry_in)
    return result

class ARMEmulator(object):
    """
    ARMEmulator is an ARM/THUMB emulator capable of
    emulating instructions in a symbolic or concrete state.
    """
    def __init__(self, memory_map):
        self.flags_map = {}
        self.register_map = {}
        self.memory_map = memory_map
        self.log = logging.getLogger("ARMEmulator")
        
        self.__init_flags_map__()
        self.__init_register_map__()
   
    def __init_register_map__(self):
        """
        Initialize general purpose registers.
        """
        self.log.debug("Initialized register map")
        
        self.register_map[ARMRegister.R0] = 0
        self.register_map[ARMRegister.R1] = 0
        self.register_map[ARMRegister.R2] = 0
        self.register_map[ARMRegister.R3] = 0
        self.register_map[ARMRegister.R4] = 0
        self.register_map[ARMRegister.R5] = 0
        self.register_map[ARMRegister.R6] = 0
        self.register_map[ARMRegister.R7] = 0
        self.register_map[ARMRegister.R8] = 0
        self.register_map[ARMRegister.R9] = 0
        self.register_map[ARMRegister.R10] = 0
        self.register_map[ARMRegister.R11] = 0
        self.register_map[ARMRegister.R12] = 0
        self.register_map[ARMRegister.R13] = 0
        self.register_map[ARMRegister.R14] = 0
        self.register_map[ARMRegister.R15] = 0
   
    def __init_flags_map__(self):
        """
        Initialize processor flags to an initial state.
        """
        self.log.debug("Initialized flags map")
        
        self.flags_map[ARMFLag.N] = 0
        self.flags_map[ARMFLag.C] = 0
        self.flags_map[ARMFLag.V] = 0
        self.flags_map[ARMFLag.Z] = 0
       
    def CurrentCondition(self, opcode):
        pass
    
    def ConditionPassed(self, ins):
        """
        TODO: Implement this.
        """
        return True
    
    def getCurrentMode(self):
        return ARMMode.ARM
    
    def getRegister(self, register):
        self.log.debug("Reading register %s" % register)
        
        # Get the value of the register from the register map
        reg_val = self.register_map[register.n]
        
        # Fixup PC value
        if register.n == ARMRegister.PC:
            if self.getCurrentMode() == ARMMode.ARM:
                reg_val += 8
                
            else:
                reg_val += 4
                
        return reg_val
    
    def setRegister(self, register, value):
        self.log.debug("Setting register %s = %d " % (register, value))
        self.register_map[register.n] = value
    
    def getFlag(self, flag):
        self.log.debug("Reading flag %s" % flag)
        flag_val = self.flags_map[flag]
        return flag_val
    
    def setFlag(self, flag, value):
        self.log.debug("Setting flag %s to %d" % (flag, value))
        self.flags_map[flag] = value
            
    def ArchVersion(self):
        """
        Return the processor version.
        """
        return ARMv7
    
    def CurrentInstrSet(self):
        """
        Get the current instruction set (ARM or THUMB).
        """
        return self.arm_mode
    
    def SelectInstrSet(self, mode):
        """
        Set the current instruction set (ARM or THUMB).
        """
        self.arm_mode = mode
    
    def BranchTo(self, address):
        """
        Sets PC to 'address'
        """
        self.setRegister(ARMRegister.PC, address)
    
    def BXWritePC(self, address):
        """
        An interworking branch is performed by the BXWritePC() function:
        """
        if get_bit(address, 0) == 1:
            # Switch to THUMB
            self.SelectInstrSet(ARMMode.THUMB)
            self.BranchTo(address)
            
        elif get_bit(address, 1) == 0:
            # Switch to ARM
            self.SelectInstrSet(ARMMode.ARM)
            self.BranchTo(address)
        
        else:
            raise UnpredictableInstructionException()
    
    def BranchWritePC(self, address):
        """
        A simple branch is performed by the BranchWritePC() function.
        """
        if self.CurrentInstrSet() == ARMMode.ARM:
            if self.ArchVersion() < 6 and get_bits(address, 1, 0) != 0b00:
                return UnpredictableInstructionException()
            
            self.BranchTo(address & 0xfffffffc)
        
        elif self.CurrentInstrSet() == ARMMode.THUMB:
            self.BranchTo(address & 0xfffffffe)
        
        else:
            raise InvalidModeException()
    
    def ALUWritePC(self, address):
        """
        Changes to the PC register must be done with this function.
        """
        if self.ArchVersion() >= ARMv7 and self.CurrentInstrSet() == ARMMode.ARM:
            return self.BXWritePC(address)
        
        else:
            return self.BranchWritePC(address)
    
    def __write_reg_and_set_flags__(self, register, result, carry, overflow, setflags):
        """
        Auxiliary function to save the value of an operation into a register
        and set the flags of the processor accordingly. 
        """
        if register.n == ARMRegister.PC:
            self.ALUWritePC(result)
            
        else:
            self.setRegister(register, result)
            
            if setflags:
                n_flag = get_bit(result, 31)
                self.setFlag(ARMFLag.N, n_flag)
                
                z_flag = result == 0
                self.setFlag(ARMFLag.Z, z_flag)
                self.setFlag(ARMFLag.C, carry)
                self.setFlag(ARMFLag.V, overflow)
    
    def emulate_adc_immediate(self, ins):
        """
        ADC (immediate)
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            Rd, Rn, imm32 = ins.operands
            
            # Read the values of the registers, the immediate and required flags.
            Rd_val = self.getRegister(Rd)
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            carry_in = self.getFlag(ARMFLag.C)
            
            # Perform the operation.
            result, carry_out, overflow = AddWithCarry(Rn_val, imm32_val, carry_in)
            
            # Set the result and adjust flags accordingly.
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)
            
        return
    
    def emulate_adc_register(self, ins):
        """
        ADC (register)
        """
        if self.ConditionPassed(ins):
            if ins.encoding == eEncodingA1:
                # operands = [Register(Rd), Register(Rm)]
                Rd, Rm = ins.operands
                Rn = Rd
                shift_t = 0
                shift_n = 0
                
            else:
                # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value
                
            Rd_val = self.getRegister(Rd)
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # Perform shift operation (does not set flags).
            shifted = Shift(Rm_val, shift_t, shift_n, self.getFlag(ARMFLag.C))
            
            # Perform de addition operation
            result, carry_out, overflow = AddWithCarry(Rn_val, shifted, self.getFlag(ARMFLag.C))

            # Set the result and adjust flags accordingly.
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)

    def emulate(self, ins, dump_state=False):
        if dump_state:
            print emulator.dump_state()
            print ins
        
        if ins.id == ARMInstruction.adc_immediate:
            self.emulate_adc_immediate(ins)
        
        elif ins.id == ARMInstruction.adc_register:
            self.emulate_adc_register(ins)
            
        else:
            raise InstructionNotImplementedException()

        if dump_state:
            print emulator.dump_state()
            print
        
    def dump_state(self):
        regs = []
        for i in xrange(0, 16):
            r = Register(i)
            v = self.getRegister(r)
            regs.append("%s=%x" % (r, v))
            
        flags = []
        flags.append("%s=%d" % ("C", self.getFlag(ARMFLag.C)))
        flags.append("%s=%d" % ("N", self.getFlag(ARMFLag.N)))
        flags.append("%s=%d" % ("V", self.getFlag(ARMFLag.V)))
        flags.append("%s=%d" % ("Z", self.getFlag(ARMFLag.Z)))
        
        return "Flags: [%s] - Registers: [%s]" % (", ".join(flags), ", ".join(regs))
            
            

logging.basicConfig(level=logging.INFO)

memory_map = DummyMemoryMap() 
emulator = ARMEmulator(memory_map)

ins = Instruction("ADC", True, None, [Register(ARMRegister.R0), Register(ARMRegister.R1), Immediate(100)], eEncodingA1)
ins.id = ARMInstruction.adc_immediate
emulator.emulate(ins, dump_state=True)

ins = Instruction("ADC", True, None, [Register(ARMRegister.R0), Register(ARMRegister.R1)], eEncodingA1)
ins.id = ARMInstruction.adc_register
emulator.emulate(ins, dump_state=True)
 
ins = Instruction("ADC", True, None, [Register(ARMRegister.R0), Register(ARMRegister.R1), Register(ARMRegister.R2), RegisterShift(SRType_ASR, 4)], eEncodingA2)
ins.id = ARMInstruction.adc_register
emulator.emulate(ins, dump_state=True)
