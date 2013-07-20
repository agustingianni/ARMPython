"""
Created on Jun 12, 2013

@author: anon
"""

import logging
from constants.arm import *

from arm import InstructionNotImplementedException, \
    UnpredictableInstructionException, InvalidModeException, Instruction, \
    Register, RegisterShift, ThumbExpandImm_C, ARMExpandImm_C, DecodeImmShift

from emulator.memory import DummyMemoryMap
from bits import get_bits, get_bit, SignExtend64, Align, \
    CountLeadingZeroBits, BitCount, LowestSetBit, CountTrailingZeros

class ARMProcessor(object):
    def __init__(self):
        self.USR_MODE = 0x10
        self.FIQ_MODE = 0x11
        self.IRQ_MODE = 0x12
        self.SVC_MODE = 0x13
        self.MON_MODE = 0x16
        self.ABT_MODE = 0x17
        self.UND_MODE = 0x1b
        self.SYS_MODE = 0x1f
        
        self.cpsr = {"n": 0, "z": 0, "c": 0, "v": 0, "q": 0, "e": 0, "a": 0, "i": 0, "f": 0, "t": 0, "m": 0}
        
        # SPSR: banked Saved Program Status Register.
        self.spsr_svc = {"n": 0, "z": 0, "c": 0, "v": 0, "q": 0, "e": 0, "a": 0, "i": 0, "f": 0, "t": 0, "m": 0}
        self.spsr_mon = {"n": 0, "z": 0, "c": 0, "v": 0, "q": 0, "e": 0, "a": 0, "i": 0, "f": 0, "t": 0, "m": 0}
        self.spsr_abt = {"n": 0, "z": 0, "c": 0, "v": 0, "q": 0, "e": 0, "a": 0, "i": 0, "f": 0, "t": 0, "m": 0}
        self.spsr_und = {"n": 0, "z": 0, "c": 0, "v": 0, "q": 0, "e": 0, "a": 0, "i": 0, "f": 0, "t": 0, "m": 0}
        self.spsr_irq = {"n": 0, "z": 0, "c": 0, "v": 0, "q": 0, "e": 0, "a": 0, "i": 0, "f": 0, "t": 0, "m": 0}
        self.spsr_fiq = {"n": 0, "z": 0, "c": 0, "v": 0, "q": 0, "e": 0, "a": 0, "i": 0, "f": 0, "t": 0, "m": 0}
        
        self.regs = {}
        
        # Banked registers
        self.regs_usr = {}
        self.regs_svc = {}
        self.regs_mon = {}
        self.regs_abt = {}
        self.regs_und = {}
        self.regs_irq = {}
        self.regs_fiq = {}
    
    def save(self):
        pass
    
    def restore(self):
        pass
    
    def interrupt(self):
        pass
    
    def supervisor(self):
        # svc
        pass
    
    def undefined(self):
        pass
        

def NOT(val):
    return ~val

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

class ITSession(object):
    def __init__(self):
        self.it_counter = 0
        self.it_state = 0

    def CountITSize(self, ITMask):
        """
        Number of conditional instructions.
        """
        TZ = CountTrailingZeros(ITMask)
        return 4 - TZ

    def InitIT(self, ITState):
        """
        Init ITState.
        """
        self.ITCounter = self.CountITSize(ITState & 0b1111)
        self.ITState = ITState

    def ITAdvance(self):
        """
        Update ITState if necessary.
        """
        self.ITCounter -= 1
        
        if self.ITCounter == 0:
            self.ITState = 0
        else:
            NewITState4_0 = (self.ITState & 0b11111) << 1
            self.ITState = (self.ITState & 0b11100000) | NewITState4_0

    def LastInITBlock(self):
        """
        Return true if we're the last instruction inside an IT Block.
        """
        return self.ITCounter == 1

    def InITBlock(self):
        """
        Return true if we're inside an IT Block.
        """
        return self.ITCounter != 0


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
        self.arm_mode = ARMMode.ARM
        self.__init_flags_map__()
        self.__init_register_map__()
        
        self.it_session = ITSession()
   
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
    
    def UnalignedSupport(self):
        """
        This function returns TRUE if the processor currently provides support for unaligned memory accesses, or FALSE
        otherwise. This is always TRUE in ARMv7, controllable by the SCTLR.U bit in ARMv6, and always FALSE before
        ARMv6.
        """
        if self.ArchVersion() == ARMv7:
            return True
        elif self.ArchVersion() == ARMv6:
            # TODO: Implement this
            raise "Implement SCTLR.U"
        else:
            return False
    
    def ConditionPassed(self, ins):
        """
        boolean ConditionPassed() cond = CurrentCond();
        
        // Evaluate base condition.
        case cond<3:1> of
            when �000� result = (APSR.Z == �1�);
            when �001� result = (APSR.C == �1�);
            when �010� result = (APSR.N == �1�);
            when �011� result = (APSR.V == �1�);
            when �100� result = (APSR.C == �1�) && (APSR.Z == �0�);
            when �101� result = (APSR.N == APSR.V);
            when �110� result = (APSR.N == APSR.V) && (APSR.Z == �0�);
            when �111� result = TRUE;

        // Condition bits �111x� indicate the instruction is always executed. Otherwise, 
        // invert condition if necessary.
        if cond<0> == �1� && cond != �1111� then
            result = !result; 
        
        return result;        
        """
        cond = get_bits(ins, 0, 0)
        cond_3_1 = get_bits(cond, 3, 1)
        
        if cond_3_1 == 0b000:
            result = self.getZeroFlag() == 1
        elif cond_3_1 == 0b001:
            result = self.getCarryFlag() == 1
        elif cond_3_1 == 0b010:
            result = self.getNFlag() == 1
        elif cond_3_1 == 0b011:
            result = self.getCarryFlag() == 1
        
        return True
    
    def getCurrentMode(self):
        """
        Get current processor mode.
        """
        return self.arm_mode
    
    def setCurrentMode(self, mode):
        """
        Set current processor mode.
        """
        self.arm_mode = mode
    
    def getRegister(self, register):
        """
        Return the value of a register. Special case for the PC
        register that should be PC + 4 in the case of THUMB
        and PC + 8 in the case of ARM.
        """
        # I fail at duck typing.
        if type(register) in [type(int), type(long)]:
            register = Register(register)

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
        """
        Set the value of a register.
        """
        # I fail at duck typing.
        if type(register) in [type(int), type(long)]:
            register = Register(register)
            
        self.log.debug("Setting register %s = %d " % (register, value))
        self.register_map[register.n] = value
    
    def getFlag(self, flag):
        """
        Return the value of a flag.
        """
        self.log.debug("Reading flag %s" % flag)
        flag_val = self.flags_map[flag]
        return flag_val
    
    def setFlag(self, flag, value):
        """
        Set the value of a flag.
        """
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
        return self.getCurrentMode()
    
    def SelectInstrSet(self, mode):
        """
        Set the current instruction set (ARM or THUMB).
        """
        return self.setCurrentMode(mode)
    
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
    
    def LoadWritePC(self, address):
        """
        The LoadWritePC() and ALUWritePC() functions are used for two cases where the behavior was systematically
        modified between architecture versions
        """
        if self.ArchVersion() >= ARMv5T:
            self.BXWritePC(address)
        
        else:
            self.BranchWritePC(address)
    
    def ALUWritePC(self, address):
        """
        Changes to the PC register must be done with this function.
        """
        if self.ArchVersion() >= ARMv7 and self.CurrentInstrSet() == ARMMode.ARM:
            return self.BXWritePC(address)
        
        else:
            return self.BranchWritePC(address)
    
    def __write_reg_and_set_flags__(self, register, result, carry=None, overflow=None, setflags=False):
        """
        Auxiliary function to save the value of an operation into a register
        and set the flags of the processor accordingly. 
        """
        if register == ARMRegister.PC:
            self.ALUWritePC(result)
            
        else:
            self.setRegister(register, result)
            
            if setflags:
                n_flag = get_bit(result, 31)
                self.setFlag(ARMFLag.N, n_flag)
                
                z_flag = int(result == 0)
                self.setFlag(ARMFLag.Z, z_flag)
                
                if carry != None:
                    self.setFlag(ARMFLag.C, carry)
                
                if overflow != None:
                    self.setFlag(ARMFLag.V, overflow)
    
    def emulate_adc_immediate(self, ins):
        """
        ADC (immediate)
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            Rd, Rn, imm32 = ins.operands
            
            # Read the values of the registers, the immediate and required flags.
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            carry_in = self.getCarryFlag()
            
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
                
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # Perform shift operation (does not set flags).
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # Perform de addition operation
            result, carry_out, overflow = AddWithCarry(Rn_val, shifted, self.getCarryFlag())

            # Set the result and adjust flags accordingly.
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)

    def emulate_adc_rsr(self, ins):
        """
        ADC (register-shifted register)
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            shift_n = shift.value
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result, carry_out, overflow = AddWithCarry(Rn_val, shifted, self.getCarryFlag())
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)

    def emulate_add_immediate_arm(self, ins):
        """
        Done
        """
        # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
        if self.ConditionPassed(ins):
            Rd, Rn, imm32 = ins.operands
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            
            # (result, carry, overflow) = AddWithCarry(R[n], imm32, '0');
            result, carry_out, overflow = AddWithCarry(Rn_val, imm32_val, 0)
            
            # Set the result and adjust flags accordingly.
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)

    def emulate_add_immediate_thumb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            # operands = [Register(Rd), Immediate(imm32)]
            if len(ins.operands) == 3:
                Rd, Rn, imm32 = ins.operands
            else:
                Rd, imm32 = ins.operands
                Rn = Rd
                
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            
            # (result, carry, overflow) = AddWithCarry(R[n], imm32, '0');
            result, carry_out, overflow = AddWithCarry(Rn_val, imm32_val, 0)
            
            # R[d] = result;
            self.setRegister(Rd, result)
            
            if ins.setflags:
                n_flag = get_bit(result, 31)
                self.setFlag(ARMFLag.N, n_flag)
                
                z_flag = int(result == 0)
                self.setFlag(ARMFLag.Z, z_flag)
                
                self.setFlag(ARMFLag.C, carry_out)
                self.setFlag(ARMFLag.V, overflow)
            
    def emulate_add_register_arm(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            shift_n = shift.value
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result, carry_out, overflow = AddWithCarry(Rn_val, shifted, 0)
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)

    def emulate_add_register_thumb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):            
            if ins.encoding == eEncodingT1:
                # operands = [Register(Rd), Register(Rn), Register(Rm)]
                Rd, Rn, Rm = ins.operands
                shift_t = SRType_LSL
                shift_n = 0
            
            elif ins.encoding == eEncodingT2:
                # operands = [Register(Rd), Register(Rm)]
                Rd, Rm = ins.operands
                Rn = Rd
                shift_t = SRType_LSL
                shift_n = 0                
                 
            elif ins.encoding == eEncodingT3:
                # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value
                
            Rm_val = self.getRegister(Rm)
            Rn_val = self.getRegister(Rn)

            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result, carry_out, overflow = AddWithCarry(Rn_val, shifted, 0)
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)

    def emulate_add_rsr(self, ins):
        """
        Done
        """        
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_

            # shift_n = UInt(R[s]<7:0>);
            shift_n = get_bits(self.getRegister(shift.value), 7, 0)
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(R[n], shifted, '0');
            result, carry_out, overflow = AddWithCarry(Rn_val, shifted, 0)
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)

    def emulate_add_sp_plus_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            Rd, Rn, imm32 = ins.operands
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            
            # (result, carry, overflow) = AddWithCarry(SP, imm32, '0');
            result, carry_out, overflow = AddWithCarry(Rn_val, imm32_val, 0)
            
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)
    
    def emulate_add_sp_plus_register_thumb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(ARMRegister.SP), Register(Rm)]
            # operands = [Register(Rd), Register(Rm)]
            # operands = [Register(Rd), Register(ARMRegister.SP), Register(Rm), RegisterShift(shift_t, shift_n)]
            if len(ins.operands) == 2:
                Rd, Rm = ins.operands
                Rn = Register(ARMRegister.SP)
                shift_t = SRType_LSL
                shift_n = 0

            elif len(ins.operands) == 3:
                Rd, Rn, Rm = ins.operands
                shift_t = SRType_LSL
                shift_n = 0
            
            elif len(ins.operands) == 4:
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value    

            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(SP, shifted, '0');
            result, carry_out, overflow = AddWithCarry(Rn_val, shifted, 0)
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)

    def emulate_add_sp_plus_register_arm(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            shift_n = shift.value

            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(SP, shifted, '0');
            result, carry_out, overflow = AddWithCarry(Rn_val, shifted, 0)
            self.__write_reg_and_set_flags__(Rd, result, carry_out, overflow, ins.setflags)
            
    def emulate_adr(self, ins):
        if self.ConditionPassed(ins):
            if ins.encoding == eEncodingA1: 
                add = True
            elif ins.encoding == eEncodingA2:
                add = False
            elif ins.encoding == eEncodingT1:
                add = True
            elif ins.encoding == eEncodingT2:
                add = False
            elif ins.encoding == eEncodingT3:
                add = True

            # operands = [Register(Rd), Register(ARMRegister.PC), Immediate(imm32)]
            Rd, Rn, imm32 = ins.operands
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n

            if add:            
                result = Align(Rn_val, 4) + imm32_val
            else:
                result = Align(Rn_val, 4) - imm32_val
                
            self.__write_reg_and_set_flags__(Rd, result)

    def emulate_and_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            Rd, Rn, unused = ins.operands
            Rn_val = self.getRegister(Rn)
            
            if ins.encoding == eEncodingT1:
                # (imm32, carry) = ThumbExpandImm_C(i:imm3:imm8, APSR.C);
                imm32, carry = ThumbExpandImm_C(ins.opcode, self.getCarryFlag());
                
            elif ins.encoding == eEncodingA1:
                # (imm32, carry) = ARMExpandImm_C(imm12, APSR.C);
                imm32, carry = ARMExpandImm_C(ins.opcode, self.getCarryFlag());

            # result = R[n] AND imm32;
            result = self.getRegister(Rn) & imm32;
            
            # Does not change the overflow.
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)

    def emulate_and_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                Rd, Rm = ins.operands
                Rn = Rd
                shift_t = SRType_LSL
                shift_n = 0
                
            elif len(ins.operands) == 4:
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value

            Rm_val = self.getRegister(Rm)
            Rn_val = self.getRegister(Rn)
            
            # (shifted, carry) = Shift_C(R[m], shift_t, shift_n, APSR.C);
            shifted, carry = Shift_C(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # result = R[n] AND shifted;
            result = Rn_val & shifted
            
            # Does not change the overflow.
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
            
    def emulate_and_rsr(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            shift_n = self.getRegister(shift.value)
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # (shifted, carry) = Shift_C(R[m], shift_t, shift_n, APSR.C);
            shifted, carry = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # result = R[n] AND shifted;
            result = Rn_val & shifted
            
            # Does not change the overflow.
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
    
    def emulate_asr_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rd, Rm, imm32 = ins.operands
            Rm_val = self.getRegister(Rm)
            imm32_val = imm32.n
            
            # (result, carry) = Shift_C(R[m], SRType_ASR, shift_n, APSR.C);
            result, carry = Shift_C(Rm_val, SRType_ASR, imm32_val, self.getCarryFlag())
            
            # Does not change the overflow.
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)

    def emulate_asr_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                Rd, Rm = ins.operands
                Rn = Rd
            elif len(ins.operands) == 3:
                Rd, Rn, Rm = ins.operands

            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)

            # shift_n = UInt(R[m]<7:0>);
            shift_n = get_bits(Rm_val, 7, 0)
            
            # (result, carry) = Shift_C(R[n], SRType_ASR, shift_n, APSR.C);
            result, carry = Shift_C(Rn_val, SRType_ASR, shift_n, self.getCarryFlag())
            
            # Does not change the overflow.
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)

    def emulate_b(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            jmp = ins.operands
            self.BranchWritePC(self.self.getPC() + jmp.addr)
            
    def emulate_bic_immediate(self, ins):
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            Rd, Rn, imm32 = ins.operands
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            result = Rn_val & (NOT(imm32_val))

            # Does not change the overflow.
            self.__write_reg_and_set_flags__(Rd, result, 0, None, ins.setflags)
            
    def emulate_bic_register(self, ins):
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rm)]
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            if len(ins.operands) == 2:
                Rd, Rm = ins.operands
                Rn = Rd
                shift_t = SRType_LSL
                shift_n = 0
            
            elif len(ins.operands) == 4:
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            shifted, carry = Shift_C(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result = Rn_val & (NOT(shifted))    

            # Does not change the overflow.
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
            
    def emulate_bic_rsr(self, ins):
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            shift_n = shift.value
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            shifted, carry = Shift_C(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result = Rn_val & (NOT(shifted))
            
            # Does not change the overflow.
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)

    def BKPTInstrDebugEvent(self):
        raise Exception("BKPTInstrDebugEvent")

    def emulate_bkpt(self, ins):
        self.BKPTInstrDebugEvent()

    def emulate_bl_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Jump(imm)]
            jmp = ins.operands
            
            if self.CurrentInstrSet() == ARMMode.ARM:
                lr_val = self.self.getPC() - 4                
            else:
                lr_val = self.self.getPC() | 1
                
            self.setRegister(ARMRegister.LR, lr_val)
            
            # The target instruction set is defined on the decoding phase.
            if ins.encoding == eEncodingT1:
                # bl
                targetInstrSet = ARMMode.THUMB
            elif ins.encoding == eEncodingT2:
                # blx
                targetInstrSet = ARMMode.ARM                
            elif ins.encoding == eEncodingA1:
                # bl
                targetInstrSet = ARMMode.ARM
            elif ins.encoding == eEncodingA2:
                # blx
                targetInstrSet = ARMMode.THUMB
                
            if targetInstrSet == ARMMode.ARM:
                targetAddress = Align(self.self.getPC(), 4) + jmp.addr
            else:
                targetAddress = self.self.getPC() + jmp.addr
                
            self.SelectInstrSet(targetInstrSet)
            self.BranchWritePC(targetAddress)
            
    def getPC(self):
        return self.getRegister(ARMRegister.PC)
    
    def emulate_blx_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rm = ins.operands
            target = self.getRegister(Rm)
            if self.CurrentInstrSet() == ARMMode.ARM:
                next_instr_addr = self.getPC() - 4
                LR = next_instr_addr
            else:
                next_instr_addr = self.getPC() - 2
                LR = next_instr_addr | 1
                
            self.setRegister(ARMRegister.LR, LR)
            self.BXWritePC(target)

    def emulate_bx(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rm = ins.operands
            self.BXWritePC(self.getRegister(Rm))
            
    def emulate_bxj(self, ins):
        self.log("BXJ is not supported.")       
    
    def emulate_cbz(self, ins):
        """
        Done
        """
        Rn, imm32 = ins.operands
        Rn_val = self.getRegister(Rn)
        
        if ins.name == "CBNZ":
            nonzero = 1
        else:
            nonzero = 0
            
        if nonzero ^ (Rn_val == 0):
            self.BranchWritePC(self.getPC() + imm32.n)
    
    def emulate_cdp(self, ins):
        self.log("CDP is not supported.")
            
    def emulate_clz(self, ins):
        if self.ConditionPassed(ins):
            Rd, Rm = ins.operands
            Rm_val = self.getRegister(Rm)
            result = CountLeadingZeroBits(Rm_val)
            self.setRegister(Rd, result)
    
    def emulate_cmn_immediate(self, ins):
        if self.ConditionPassed(ins):
            Rn, imm32 = ins.operands
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            result, carry, overflow = AddWithCarry(Rn_val, imm32_val, 0)
            self.__set_flags__(result, carry, overflow)
    
    def getCarryFlag(self):
        return self.getFlag(ARMFLag.C)
    
    def getZeroFlag(self):
        return self.getFlag(ARMFLag.Z)
    
    def getOverflowFlag(self):
        return self.getFlag(ARMFLag.V)
    
    def getNFlag(self):
        return self.getFlag(ARMFLag.N)
    
    def emulate_cmn_register(self, ins):
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                Rn, Rm = ins.operands
                shift_t = SRType_LSL
                shift_n = 0
            elif len(ins.operands) == 3:
                Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value
                
            Rm_val = self.getRegister(Rm)
            Rn_val = self.getRegister(Rn)
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result, carry, overflow = AddWithCarry(Rn_val, shifted, 0)
            self.__set_flags__(result, carry, overflow)
    
    def emulate_cmn_rsr(self, ins):
        if self.ConditionPassed(ins):
            # operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            
            # Shift ammount is on a register
            shift_n = self.getRegister(shift.value)
            shift_n = get_bits(shift_n, 7, 0)
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result, carry, overflow = AddWithCarry(Rn_val, shifted, 0)
            self.__set_flags__(result, carry, overflow)

    def __set_flags__(self, result, carry=None, overflow=None):
        self.setFlag(ARMFLag.N, get_bit(result, 31))
        self.setFlag(ARMFLag.Z, int(result == 0))
        
        if carry:
            self.setFlag(ARMFLag.C, carry)
        
        if overflow:
            self.setFlag(ARMFLag.V, overflow)                
    
    def emulate_cmp_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rn, imm32 = ins.operands
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            
            # (result, carry, overflow) = AddWithCarry(R[n], NOT(imm32), '1');
            result, carry, overflow = AddWithCarry(Rn_val, NOT(imm32_val), 1)
            self.__set_flags__(result, carry, overflow)
    
    def emulate_cmp_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                Rn, Rm = ins.operands
                shift_t = SRType_LSL
                shift_n = 0                
            elif len(ins.operands) == 3:
                Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value
            
            Rm_val = self.getRegister(Rm)
            Rn_val = self.getRegister(Rn)
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(R[n], NOT(shifted), '1');
            result, carry, overflow = AddWithCarry(Rn_val, NOT(shifted), 1)
            self.__set_flags__(result, carry, overflow)
                    
    def emulate_cmp_rsr(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            
            # shift_n = UInt(R[s]<7:0>);
            shift_n = self.getRegister(shift.value)
            shift_n = get_bits(shift_n, 7, 0)
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(R[n], NOT(shifted), '1');
            result, carry, overflow = AddWithCarry(Rn_val, NOT(shifted), 1)
            self.__set_flags__(result, carry, overflow)
        
    def Hint_Debug(self, option):
        self.log("Hint_Debug")    
    
    def emulate_dbg(self, ins):
        if self.ConditionPassed(ins):
            option = ins.operands
            self.Hint_Debug(option)
    
    def emulate_eor_immediate(self, ins):
        if self.ConditionPassed(ins):
            Rd, Rn, imm32 = ins.operands
            Rn_val = self.getRegister(Rn)
            imm32_val = imm32.n
            result = Rn_val ^ imm32_val
            
            # TODO: Carry depends on the decoding of the instruction.
            carry = 0            
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
    
    def emulate_eor_register(self, ins):
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                Rn, Rm = ins.operands
                Rd = Rn
                shift_t = SRType_LSL
                shift_n = 0                
            elif len(ins.operands) == 4:
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value
            
            Rm_val = self.getRegister(Rm)
            Rn_val = self.getRegister(Rn)
            shifted, carry = Shift_C(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result = Rn_val ^ shifted
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
    
    def emulate_eor_rsr(self, ins):
        if self.ConditionPassed(ins):
            # operands = [Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            
            # Shift ammount is on a register
            shift_n = self.getRegister(shift.value)
            shift_n = get_bits(shift_n, 7, 0)
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            shifted, carry = Shift_C(Rm_val, shift_t, shift_n, self.getCarryFlag())
            result = Rn_val ^ shifted
            if ins.setflags:
                self.__set_flags__(result, carry, None)
                
    def emulate_eret(self, ins):
        raise Exception("ERET")
    
    def emulate_hvc(self, ins):
        raise Exception("HVC")
    
    def emulate_it(self, ins):
        """
        Done
        """
        self.it_session.InitIT(get_bits(ins.opcode, 7, 0))
                
    def emulate_ldc_immediate(self, ins):
        raise Exception("HVC")
        
    def emulate_ldc_literal(self, ins):
        raise Exception("HVC")
    
    def emulate_ldmda(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rn, wback), RegisterSet(registers)]
            Rn, regset = ins.operands
            registers = regset.registers
            Rn_val = self.getRegister(Rn)
            
            # address = R[n] - 4*BitCount(registers) + 4;
            address = Rn_val - 4 * BitCount(registers) + 4
            
            for i in xrange(0, 15):
                if get_bit(registers, i):
                    # R[i] = MemA[address,4]; address = address + 4;
                    value = self.memory_map.get_dword(address)
                    self.setRegister(i, value)
                    address += 4
                    
            if get_bit(registers, 15):
                self.LoadWritePC(self.memory_map.get_dword(address))
                
            # if wback && registers<n> == '0' then R[n] = R[n] - 4*BitCount(registers);
            if Rn.wback and get_bit(registers, Rn.n) == 0:
                val = Rn_val - 4 * BitCount(registers)
                self.setRegister(Rn, val)
            
            # if wback && registers<n> == '1' then R[n] = bits(32) UNKNOWN;    
            if Rn.wback and get_bit(registers, Rn.n) == 1:
                raise Exception("Rn cannot be in registers when wback is true.")
    
    def emulate_ldmdb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rn, wback), RegisterSet(registers)]
            Rn, regset = ins.operands
            registers = regset.registers
            Rn_val = self.getRegister(Rn)
            
            # address = R[n] - 4*BitCount(registers);
            address = Rn_val - 4 * BitCount(registers)
            
            for i in xrange(0, 15):
                if get_bit(registers, i):
                    # R[i] = MemA[address,4]; address = address + 4;
                    value = self.memory_map.get_dword(address)
                    self.setRegister(i, value)
                    address += 4
                    
            if get_bit(registers, 15):
                self.LoadWritePC(self.memory_map.get_dword(address))
                
            # if wback && registers<n> == '0' then R[n] = R[n] - 4*BitCount(registers);
            if Rn.wback and get_bit(registers, Rn.n) == 0:
                val = Rn_val - 4 * BitCount(registers)
                self.setRegister(Rn, val)
            
            # if wback && registers<n> == '1' then R[n] = bits(32) UNKNOWN;    
            if Rn.wback and get_bit(registers, Rn.n) == 1:
                raise Exception("Rn cannot be in registers when wback is true.")
    
    def emulate_ldm_exception_return(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldmia_arm(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 1:
                # In case we've decoded it as POP
                Rn = Register(ARMRegister.SP)
                regset = ins.operands
                registers = regset.registers
                
            else:
                Rn, registers = ins.operands
                registers = regset.registers
                
            address = self.getRegister(Rn)
            
            for i in xrange(0, 15):
                if get_bit(registers, i):
                    value = self.memory_map.get_dword(address)
                    self.setRegister(i, value)
                    address += 4
                    
            if get_bit(registers, 15):
                self.LoadWritePC(self.memory_map.get_dword(address))
                
            if Rn.wback and get_bit(registers, Rn.n) == 0:
                val = self.getRegister(Rn) + 4 * BitCount(registers)
                self.setRegister(Rn, val)
                
            elif Rn.wback and get_bit(registers, Rn.n) == 1:
                raise Exception("Rn cannot be in registers when wback is true.")
    
    def emulate_ldmia_thumb(self, ins):
        """
        Done
        """
        self.emulate_ldmia_arm(self, ins)
    
    def emulate_ldmib(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rn, wback), RegisterSet(registers)]
            Rn, regset = ins.operands
            registers = regset.registers
            Rn_val = self.getRegister(Rn)
            
            # address = R[n] + 4;
            address = Rn_val + 4
            
            for i in xrange(0, 15):
                if get_bit(registers, i):
                    # R[i] = MemA[address,4]; address = address + 4;
                    value = self.memory_map.get_dword(address)
                    self.setRegister(i, value)
                    address += 4
                    
            if get_bit(registers, 15):
                self.LoadWritePC(self.memory_map.get_dword(address))
                
            # if wback && registers<n> == '0' then R[n] = R[n] - 4*BitCount(registers);
            if Rn.wback and get_bit(registers, Rn.n) == 0:
                val = Rn_val + 4 * BitCount(registers)
                self.setRegister(Rn, val)
            
            # if wback && registers<n> == '1' then R[n] = bits(32) UNKNOWN;    
            if Rn.wback and get_bit(registers, Rn.n) == 1:
                raise Exception("Rn cannot be in registers when wback is true.")
    
    def emulate_ldm_user_registers(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrb_immediate_arm(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrb_immediate_thumb(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrb_literal(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrb_register(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrbt(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrexb(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrexd(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrexh(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldrex(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ldr_immediate_arm(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rt), Memory(Register(Rn), None, Immediate(imm12), wback)]
            # operands = [Register(Rt), Memory(Register(Rn), None, Immediate(imm12), wback)]
            # operands = [Register(Rt), Memory(Register(Rn), None, None            , wback), Immediate(imm12)]
            
            if len(ins.operands) == 2:
                # Deal with the indexed form of the opcode
                index = True
                Rt, mem = ins.operands
                Rn, imm32 = mem.op1, mem.op3
                wback = mem.wback
                
            else:
                # Deal with the non indexed form of the opcode.
                index = False
                Rt, mem, imm32 = ins.operands
                Rn = mem.op1
                wback = mem.wback                
            
            # offset_addr = if add then (R[n] + imm32) else (R[n] - imm32);
            offset_addr = self.getRegister(Rn) + imm32.n
            
            # address = if index then offset_addr else R[n];
            if index:
                address = offset_addr
            else:
                address = self.getRegister(Rn)
            
            # data = MemU[address,4];
            data = self.memory_map.get_dword(address)
            
            # if wback then R[n] = offset_addr;
            if wback:
                self.setRegister(Rn, offset_addr)
                
            if Rt.n == ARMRegister.PC:
                if get_bits(address, 1, 0) == 0b00:
                    self.LoadWritePC(data)
                else:
                    raise UnpredictableInstructionException()
            
            elif self.UnalignedSupport() or get_bits(address, 1, 0) == 0b00:
                self.setRegister(Rt, data)
                
            else:
                self.setRegister(Rt, ROR(data, 8 * get_bits(address, 1, 0)))
    
    def emulate_ldr_immediate_thumb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rt), Memory(Register(Rn), None, Immediate(imm12), wback)]
            # operands = [Register(Rt), Memory(Register(Rn), None, Immediate(imm12), wback)]
            # operands = [Register(Rt), Memory(Register(Rn), None, None            , wback), Immediate(imm12)]
            
            if len(ins.operands) == 2:
                # Deal with the indexed form of the opcode
                index = True
                Rt, mem = ins.operands
                Rn, imm32 = mem.op1, mem.op3
                wback = mem.wback
                
            else:
                # Deal with the non indexed form of the opcode.
                index = False
                Rt, mem, imm32 = ins.operands
                Rn = mem.op1
                wback = mem.wback                
            
            # offset_addr = if add then (R[n] + imm32) else (R[n] - imm32);
            offset_addr = self.getRegister(Rn) + imm32.n
            
            # address = if index then offset_addr else R[n];
            if index:
                address = offset_addr
            else:
                address = self.getRegister(Rn)
            
            # data = MemU[address,4];
            data = self.memory_map.get_dword(address)
            
            # if wback then R[n] = offset_addr;
            if wback:
                self.setRegister(Rn, offset_addr)
                
            if Rt.n == ARMRegister.PC:
                if get_bits(address, 1, 0) == 0b00:
                    self.LoadWritePC(data)
                else:
                    raise UnpredictableInstructionException()
            
            elif self.UnalignedSupport() or get_bits(address, 1, 0) == 0b00:
                self.setRegister(Rt, data)
                
            else:
                # TODO: ???
                # else R[t] = bits(32) UNKNOWN; // Can only apply before ARMv7
                self.setRegister(Rt, 0)
            
    def emulate_ldr_literal(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                Rt, imm32 = ins.operands
                Rt_val = self.getRegister(Rt)
                imm32_val = imm32.n
                
            else:
                Rt, memory = ins.operands
                Rt_val = self.getRegister(Rt)
                imm32 = memory.op2
                imm32_val = imm32.n

            
            PC = self.getPC()
            base = Align(PC, 4)
            
            # address = if add then (base + imm32) else (base - imm32);
            address = base + imm32.n
            
            # data = MemU[address,4];
            data = self.memory_map.get_dword(address)

            if Rt.n == ARMRegister.PC:
                if get_bits(address, 1, 0) == 0b00:
                    self.LoadWritePC(data)
                else:
                    raise UnpredictableInstructionException()
            
            elif self.UnalignedSupport() or get_bits(address, 1, 0) == 0b00:
                self.setRegister(Rt, data)
                
            else:
                if self.CurrentInstrSet() == ARMMode.ARM:
                    # R[t] = ROR(data, 8*UInt(address<1:0>));
                    self.setRegister(Rt, ROR(data, 8 * get_bits(address, 1, 0)))
                    
                else:
                    # TODO: ???
                    # R[t] = bits(32) UNKNOWN;
                    self.setRegister(Rt, 0)

    
    def emulate_ldr_register_arm(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                index = True
                Rt, memory = ins.operands
                Rn = memory.op1
                Rm = memory.op2
                shift_t = memory.op3.type_
                shift_n = memory.op3.value
                wback = memory.wback
                
            else:
                index = False
                Rt, memory, Rm, shift = ins.operands
                Rn = memory.op1
                shift_t = shift.type_
                shift_n = shift.value
                wback = False
                
            # offset = Shift(R[m], shift_t, shift_n, APSR.C);
            offset = Shift(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag())
            
            # offset_addr = if add then (R[n] + offset) else (R[n] - offset);
            offset_addr = self.getRegister(Rn) + offset
            
            # address = if index then offset_addr else R[n];
            if index:
                address = offset_addr
            else:
                address = self.getRegister(Rn)
                
            # data = MemU[address,4];
            data = self.memory_map.get_dword(address)
            
            # if wback then R[n] = offset_addr;
            if wback:
                self.setRegister(Rn, offset_addr)
                
            if Rt.n == ARMRegister.PC:
                if get_bits(address, 1, 0) == 0b00:
                    self.LoadWritePC(data)
                else:
                    raise UnpredictableInstructionException()
                
            elif self.UnalignedSupport() or get_bits(address, 1, 0) == 0b00:
                self.setRegister(Rt, data)
                
            else:
                # R[t] = ROR(data, 8*UInt(address<1:0>));
                self.setRegister(Rt, ROR(data, 8 * get_bits(address, 1, 0)))
    
    def emulate_ldr_register_thumb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rt, memory = ins.operands
            Rn = memory.op1
            Rm = memory.op2
            
            if not memory.op3:
                # Default shift values
                shift_t = SRType_LSL
                shift_n = 0
                
            else:
                shift_t = memory.op3.type_
                shift_n = memory.op3.value  
            
            # offset = Shift(R[m], shift_t, shift_n, APSR.C);
            offset = Shift(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag())
            
            # offset_addr = (R[n] + offset);
            offset_addr = self.getRegister(Rn) + offset
            
            address = offset_addr
            
            # data = MemU[address,4];
            data = self.memory_map.get_dword(address)
            
            if Rt.n == ARMRegister.PC:
                if get_bits(address, 1, 0) == 0b00:
                    self.LoadWritePC(data)
                else:
                    raise UnpredictableInstructionException()
                
            elif self.UnalignedSupport() or get_bits(address, 1, 0) == 0b00:
                self.setRegister(Rt, data)
            
    
    def emulate_ldrt(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_lsl_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            Rd, Rm, imm32 = ins.operands
            
            # (-, shift_n) = DecodeImmShift('00', imm5);
            t, shift_n = DecodeImmShift(0b00, imm32.n)
            
            # (result, carry) = Shift_C(R[m], SRType_LSL, shift_n, APSR.C);
            result, carry = Shift_C(self.getRegister(Rm), SRType_LSL, shift_n, self.getCarryFlag());
    
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
            
    
    def emulate_lsl_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                Rd, Rm  = ins.operands
                Rn = Rd
            else:
                Rd, Rn, Rm = ins.operands
                
        # shift_n = UInt(R[m]<7:0>);
        shift_n = get_bits(self.getRegister(Rm), 7, 0)
        
        # (result, carry) = Shift_C(R[n], SRType_LSL, shift_n, APSR.C);
        result, carry = Shift_C(self.getRegister(Rn), SRType_LSL, shift_n, self.getCarryFlag());
            
        # R[d] = result;
        self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)

    
    def emulate_lsr_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rm), Immediate(imm5)]
            Rd, Rm, imm32 = ins.operands
            
            shift_n = imm32.n
            
            # (result, carry) = Shift_C(R[m], SRType_LSR, shift_n, APSR.C);
            result, carry = Shift_C(self.getRegister(Rm), SRType_LSR, shift_n, self.getCarryFlag());
            
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
    
    def emulate_lsr_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if ins.encoding == eEncodingT1:
                # operands = [Register(Rd), Register(Rm)]
                Rd, Rm = ins.operands
                Rn = Rd
                
            else:
                # operands = [Register(Rd), Register(Rn), Register(Rm)]
                Rd, Rn, Rm = ins.operands
                
            # shift_n = UInt(R[m]<7:0>);
            shift_n = get_bits(self.getRegister(Rm), 7, 0)
            
            # (result, carry) = Shift_C(R[n], SRType_LSR, shift_n, APSR.C);
            result, carry = Shift_C(self.getRegister(Rn), SRType_LSR, shift_n, self.getCarryFlag())
            
            self.__set_flags__(result, carry, None)            
    
    def emulate_mcrr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mcr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mla(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), Register(Ra)]
            Rd, Rn, Rm, Ra = ins.operands
            
            # operand1 = SInt(R[n]); // operand1 = UInt(R[n]) produces the same final results
            operand1 = self.getRegister(Rn)
            
            # operand2 = SInt(R[m]); // operand2 = UInt(R[m]) produces the same final results
            operand2 = self.getRegister(Rm)
            
            # addend = SInt(R[a]); // addend = UInt(R[a]) produces the same final results
            addend = self.getRegister(Ra)
            
            # result = operand1 * operand2 + addend;
            result = operand1 * operand2 + addend
            
            # R[d] = result<31:0>;
            self.setRegister(Rd, get_bits(result, 31, 0))
            
            self.__set_flags__(result, None, None)
    
    def emulate_mls(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mov_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Immediate(imm32)]
            Rd, immediate = ins.operands
            
            if ins.encoding == eEncodingT1:
                carry = self.getCarryFlag()
                immediate_val = immediate.n
            
            elif ins.encoding == eEncodingT2:
                immediate_val, carry = ThumbExpandImm_C(ins.opcode, self.getCarryFlag())
            
            elif ins.encoding == eEncodingA1:
                immediate_val, carry = ARMExpandImm_C(ins.opcode, self.getCarryFlag())
            
            else:
                # In other encodings setflags == False so no carry is set
                immediate_val = immediate.n
                carry = None
            
            if Rd.n == ARMRegister.PC:
                self.ALUWritePC(immediate_val)
                
            else:
                self.__write_reg_and_set_flags__(Rd, immediate_val, carry, None, ins.setflags)
    
    def emulate_mov_register_arm(self, ins):
        """
        Done
        """        
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rm)]
            Rd, Rm = ins.operands
            
            if Rd.n == ARMRegister.PC:
                self.ALUWritePC(self.getRegister(Rm))
            
            else:
                self.__write_reg_and_set_flags__(Rd, self.getRegister(Rm), None, None, ins.setflags)
    
    def emulate_mov_register_thumb(self, ins):
        """
        Done
        """
        # Same as ARM version.
        self.emulate_mov_register_arm(ins)
    
    def emulate_mov_rsr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_movt(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mrc(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mrrc(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mrs(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_msr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mull(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mul(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm)]
            Rd, Rn, Rm = ins.operands
            
            # operand1 = SInt(R[n]); // operand1 = UInt(R[n]) produces the same final results
            operand1 = self.getRegister(Rn)
            
            # operand2 = SInt(R[m]); // operand2 = UInt(R[m]) produces the same final results
            operand2 = self.getRegister(Rm)
            
            # result = operand1 * operand2;
            result = operand1 * operand2
            
            # R[d] = result<31:0>;
            self.setRegister(Rd, get_bits(result, 31, 0))
            
            self.__set_flags__(result, None, None)
                
    def emulate_mvn_immediate(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mvn_register(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_mvn_rsr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_nop(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_orr_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]

            Rd, Rn, t = ins.operands

            if ins.encoding == eEncodingT1:
                immediate_val, carry = ThumbExpandImm_C(ins.opcode, self.getCarryFlag())
                
            elif ins.encoding == eEncodingA1:
                immediate_val, carry = ARMExpandImm_C(ins.opcode, self.getCarryFlag())
                
            # result = R[n] OR imm32;
            result = self.getRegister(Rn) | immediate_val
            
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
    
    def emulate_orr_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if ins.encoding == eEncodingT1:
                # operands = [Register(Rd), Register(Rm)]
                Rd, Rm = ins.operands
                Rn = Rd
                shift_t = SRType_LSL
                shift_n = 0
    
            elif ins.encoding == eEncodingT2:
                # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value
                
            elif ins.encoding == eEncodingA1:
                # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value
            
            # (shifted, carry) = Shift_C(R[m], shift_t, shift_n, APSR.C);
            shifted, carry = Shift_C(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag())
            
            # result = R[n] OR shifted;
            result = self.getRegister(Rn) | shifted
            
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)            
    
    def emulate_orr_rsr(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_

            # shift_n = UInt(R[s]<7:0>);
            shift_n = get_bits(self.getRegister(shift.value), 7, 0)
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # (shifted, carry) = Shift_C(R[m], shift_t, shift_n, APSR.C);
            shifted, carry = Shift_C(Rm_val, shift_t, shift_n, self.getCarryFlag())
            
            # result = R[n] OR shifted;
            result = Rn_val | shifted
            
            self.__write_reg_and_set_flags__(Rd, result, carry, None, ins.setflags)
    
    def emulate_pld(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_pop_arm(self, ins):
        """
        operands = [RegisterSet(registers)]
        """
        # Same as THUMB
        self.emulate_pop_thumb(ins)
    
    def emulate_pop_thumb(self, ins):
        """
        """
        if self.ConditionPassed(ins):
            # Unaligned is only allowed on T3
            UnalignedAllowed = ins.encoding == eEncodingT3
            
            regset = ins.operands
            registers = regset.registers
            
            # address = SP;
            address = self.getRegister(Register(ARMRegister.SP))
            
            # for i = 0 to 14
            for i in xrange(0, 14 + 1):
                if get_bit(registers, i):
                    self.setRegister(Register(i), self.memory_map.get_dword(address))
                    address = address + 4
                    
            if get_bit(registers, 15) == 1:
                if UnalignedAllowed:
                    if get_bits(address, 1, 0) == 0b00:
                        self.LoadWritePC(self.memory_map.get_dword(address))
                    else:
                        raise UnpredictableInstructionException()
                else:
                    self.LoadWritePC(self.memory_map.get_dword(address))
                    
            if get_bit(registers, 13) == 0:
                sp_val = Register(ARMRegister.SP)
                self.setRegister(Register(ARMRegister.SP), sp_val + 4 * BitCount(registers))
            
            if get_bit(registers, 13) == 1:
                raise "if registers<13> == '1' then SP = bits(32) UNKNOWN;"
    
    def emulate_push(self, ins):
        """
        
        """
        if self.ConditionPassed(ins):
            regset = ins.operands
            registers = regset.registers
            
            UnalignedAllowed = ins.encoding == eEncodingT3 or ins.encoding == eEncodingA2
            
            # address = SP - 4*BitCount(registers);
            address = self.getRegister(Register(ARMRegister.SP)) - 4 * BitCount(registers)
            
            # for i = 0 to 14
            for i in xrange(0, 14 + 1):
                if get_bit(registers, i) == 1:
                    if i == ARMRegister.SP and i != LowestSetBit(registers):
                        raise "MemA[address,4] = bits(32) UNKNOWN;"
                    else:
                        self.memory_map.set_dword(address, self.getRegister(Register(i)))
                        
                    address = address + 4
            
            if get_bit(registers, ARMRegister.PC):
                # MemA[address,4] = PCStoreValue();
                self.memory_map.set_dword(address, self.getPC())
                
            # SP = SP - 4*BitCount(registers);
            sp_val = self.getRegister(Register(ARMRegister.SP))
            self.setRegister(Register(ARMRegister.SP), sp_val - 4 * BitCount(registers))
                            
    
    def emulate_rfe(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ror_immediate(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_ror_register(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_rrx(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_rsb_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            Rd, Rn, imm32 = ins.operands
            
            # (result, carry, overflow) = AddWithCarry(NOT(R[n]), imm32, '1');
            result, carry, overflow = AddWithCarry(NOT(self.getRegister(Rn)), imm32.n, 1)
            
            self.__write_reg_and_set_flags__(Rd, result, carry, overflow, ins.setflags)
    
    def emulate_rsb_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n)]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            shift_n  = shift.value
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(NOT(R[n]), shifted, '1');
            result, carry, overflow = AddWithCarry(NOT(self.getRegister(Rn)), shifted, 1)
            
            self.__write_reg_and_set_flags__(Rd, result, carry, overflow, ins.setflags)
            
    def emulate_rsb_rsr(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Register(Rm), RegisterShift(shift_t, Register(Rs))]
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_

            # shift_n = UInt(R[s]<7:0>);
            shift_n = get_bits(self.getRegister(shift.value), 7, 0)
            
            Rn_val = self.getRegister(Rn)
            Rm_val = self.getRegister(Rm)
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag());
            
            # (result, carry, overflow) = AddWithCarry(NOT(R[n]), shifted, '1');
            result, carry, overflow = AddWithCarry(NOT(self.getRegister(Rn)), shifted, 1);
            
            # R[d] = result;
            self.setRegister(Rd, result)
            
            self.__write_reg_and_set_flags__(Rd, result, carry, overflow, ins.setflags)
    
    def emulate_rsc_immediate(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_rsc_register(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_rsc_rsr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_sat_add_and_sub(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_sbc_immediate(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_sbc_register(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_sbc_rsr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_sev(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_smc(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_smlalb(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_smlal(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_smla(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_smlaw(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_smull(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_smul(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_smulw(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_srs_arm(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_srs_thumb(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_stc(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_stmda(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rn, wback), RegisterSet(registers)]
            Rn, regset = ins.operands
            registers = regset.registers
            
            # address = R[n] - 4*BitCount(registers) + 4;
            address = self.getRegister(Rn) - 4 * BitCount(registers) + 4
            
            for i in xrange(0, 14 + 1):
                if get_bit(registers, i):
                    if i == Rn.n and Rn.wback and i != LowestSetBit(registers):
                        raise "MemA[address,4] = bits(32) UNKNOWN; // Only possible for encodings T1 and A1"

                    else:
                        self.memory_map.set_dword(address, self.getRegister(Register(i)))
                        
                    address = address + 4
            
            if get_bit(registers, 15):
                self.memory_map.set_dword(address, self.getPC())
                
            if Rn.wback:
                Rn_val = self.getRegister(Rn)
                self.setRegister(Rn, Rn_val - 4 * BitCount(registers))
    
    def emulate_stmdb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rn, wback), RegisterSet(registers)]
            Rn, regset = ins.operands
            registers = regset.registers
            
            # address = R[n] - 4*BitCount(registers);
            address = self.getRegister(Rn) - 4 * BitCount(registers)
            
            for i in xrange(0, 14 + 1):
                if get_bit(registers, i):
                    if i == Rn.n and Rn.wback and i != LowestSetBit(registers):
                        raise "MemA[address,4] = bits(32) UNKNOWN; // Only possible for encodings T1 and A1"

                    else:
                        self.memory_map.set_dword(address, self.getRegister(Register(i)))
                        
                    address = address + 4
            
            if get_bit(registers, 15):
                self.memory_map.set_dword(address, self.getPC())
                
            if Rn.wback:
                Rn_val = self.getRegister(Rn)
                self.setRegister(Rn, Rn_val - 4 * BitCount(registers))
    
    def emulate_stmia(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rn, wback), RegisterSet(registers)]
            Rn, regset = ins.operands
            registers = regset.registers
            
            # address = R[n];
            address = self.getRegister(Rn)
            
            for i in xrange(0, 14 + 1):
                if get_bit(registers, i):
                    if i == Rn.n and Rn.wback and i != LowestSetBit(registers):
                        raise "MemA[address,4] = bits(32) UNKNOWN; // Only possible for encodings T1 and A1"

                    else:
                        self.memory_map.set_dword(address, self.getRegister(Register(i)))
                        
                    address = address + 4
            
            if get_bit(registers, 15):
                self.memory_map.set_dword(address, self.getPC())
                
            if Rn.wback:
                Rn_val = self.getRegister(Rn)
                self.setRegister(Rn, Rn_val + 4 * BitCount(registers))
    
    def emulate_stmib(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rn, wback), RegisterSet(registers)]
            Rn, regset = ins.operands
            registers = regset.registers
            
            # address = R[n] + 4;
            address = self.getRegister(Rn) + 4
            
            for i in xrange(0, 14 + 1):
                if get_bit(registers, i):
                    if i == Rn.n and Rn.wback and i != LowestSetBit(registers):
                        raise "MemA[address,4] = bits(32) UNKNOWN; // Only possible for encodings T1 and A1"

                    else:
                        self.memory_map.set_dword(address, self.getRegister(Register(i)))
                        
                    address = address + 4
            
            if get_bit(registers, 15):
                self.memory_map.set_dword(address, self.getPC())
                
            if Rn.wback:
                Rn_val = self.getRegister(Rn)
                self.setRegister(Rn, Rn_val + 4 * BitCount(registers))
    
    def emulate_stm_user_registers(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_strb_immediate_arm(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_strb_immediate_thumb(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_strb_register(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_strbt(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_strexb(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_strexd(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_strexh(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_strex(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_str_immediate_arm(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                index = True
                Rt, memory = ins.operands
                Rn = memory.op1
                imm32 = memory.op2
                wback = memory.wback
                
            else:
                index = False
                wback = True
                Rt, memory, imm32 = ins.operands
                Rn = memory.op1
            
            # offset_addr = if add then (R[n] + imm32) else (R[n] - imm32);
            offset_addr = self.getRegister(Rn) + imm32.n
            
            # address = if index then offset_addr else R[n];
            if index:
                address = offset_addr
            else:
                address = self.getRegister(Rn)
                
            # MemU[address,4] = if t == 15 then PCStoreValue() else R[t];
            if Rt.n == ARMRegister.PC:
                self.memory_map.set_dword(address, self.getPC())
            else:
                self.memory_map.set_dword(address, self.getRegister(Rt))
                
            # if wback then R[n] = offset_addr;
            if wback:
                self.setRegister(Rn, offset_addr)
                            
        
    def emulate_str_immediate_thumb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):

            if ins.encoding == eEncodingT4:
                # NOTE: I do not like the fact that I have to re decode.
                P = get_bit(ins.opcode, 10)
                W = get_bit(ins.opcode, 8)
                index = P == 1
                wback = W == 1

                if index == True:
                    Rt, memory = ins.operands
                    Rn = memory.op1
                    imm32 = memory.op2
            
                else:
                    # operands = [Register(Rt), Memory(Register(Rn)), Immediate(imm32)]
                    Rt, memory, imm32 = ins.operands
                    Rn = memory.op1

            else:
                index = True
                wback = False
                
                # operands = [Register(Rt), Memory(Register(Rn), Immediate(imm32))]
                Rt, memory = ins.operands
                Rn = memory.op1
                imm32 = memory.op2
                
            # offset_addr = if add then (R[n] + imm32) else (R[n] - imm32);
            offset_addr = self.getRegister(Rn) + imm32.n
            
            # address = if index then offset_addr else R[n];
            if index:
                address = offset_addr
            else:
                address = self.getRegister(Rn)
                
            # if UnalignedSupport() || address<1:0> == '00' then
            if self.UnalignedSupport() or get_bits(address, 1, 0) == 0b00:
                # MemU[address,4] = R[t];
                self.memory_map.set_dword(address, self.getRegister(Rt))
            else:
                # MemU[address,4] = bits(32) UNKNOWN;
                raise "MemU[address,4] = bits(32) UNKNOWN;"
            
            # if wback then R[n] = offset_addr;
            if wback :
                self.setRegister(Rn, offset_addr)
    
    def emulate_str_reg(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if ins.encoding == eEncodingA1:
                P = get_bit(ins.opcode, 24)
                U = get_bit(ins.opcode, 23)
                W = get_bit(ins.opcode, 21)

                # add is important here since the register may be negative
                index = P == 1
                add = U == 1
                wback = P == 0 or W == 1

                if index == True:
                    # operands = [Register(Rt), Memory(Register(Rn), Register(Rm, False, add == False), RegisterShift(shift_t, shift_n), wback=False)]
                    Rt, memory = ins.operands
                    Rn = memory.op1
                    Rm = memory.op2
                    shift_t = memory.op3.type_
                    shift_n = memory.op3.value
                    
                else:
                    # operands = [Register(Rt), Memory(Register(Rn)), Register(Rm, False, add == False), RegisterShift(shift_t, shift_n)]
                    Rt, memory, Rm, shift = ins.operands
                    Rn = memory.op1
                    shift_t = shift.type_
                    shift_n = shift.value

            else:
                index = True
                add = True
                wback = False
                
                # operands = [Register(Rt), Memory(Register(Rn), Register(Rm))]
                # operands = [Register(Rt), Memory(Register(Rn), Register(Rm), RegisterShift(shift_t, shift_n))]
                Rt, memory = ins.operands
                Rn = memory.op1
                Rm = memory.op2
                if memory.op3:
                    shift_t = memory.op3.type_
                    shift_n = memory.op3.value
                else:
                    shift_t = SRType_LSL
                    shift_n = 0 
    
            # papa
            # offset = Shift(R[m], shift_t, shift_n, APSR.C);
            offset = Shift(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag())
            
            # offset_addr = if add then (R[n] + offset) else (R[n] - offset);
            if add:
                offset_addr = self.getRegister(Rn) + offset
            else:
                offset_addr = self.getRegister(Rn) - offset
                
            # address = if index then offset_addr else R[n];
            if index:
                address = offset_addr
            else:
                address = self.getRegister(Rn)
                
            if Rt.n == ARMRegister.PC:
                data = self.getPC()
            else:
                data = self.getRegister(Rt)

            if self.UnalignedSupport() or get_bits(address, 1, 0) == 0b00 or self.CurrentInstrSet() == ARMMode.ARM:
                self.memory_map.set_dword(address, data)
            else:
                raise "MemU[address,4] = bits(32) UNKNOWN;"
            
            if wback:
                self.setRegister(Rn, offset_addr)
            
    
    def emulate_strt(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_sub_immediate_arm(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            # operands = [Register(Rd), Register(Rn), Immediate(imm32)]
            Rd, Rn, imm32 = ins.operands
            
            # (result, carry, overflow) = AddWithCarry(R[n], NOT(imm32), '1');
            Rn_val = self.getRegister(Rn)
            result, carry, overflow = AddWithCarry(Rn_val, NOT(imm32.n), 1)
            
            self.__write_reg_and_set_flags__(Rd, result, carry, overflow, ins.setflags)        
    
    def emulate_sub_immediate_thumb(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 2:
                Rd, imm32 = ins.operands
                Rn = Rd
            else:
                Rd, Rn, imm32 = ins.operands

            # (result, carry, overflow) = AddWithCarry(R[n], NOT(imm32), '1');
            Rn_val = self.getRegister(Rn)
            result, carry, overflow = AddWithCarry(Rn_val, NOT(imm32.n), 1)            
            self.__write_reg_and_set_flags__(Rd, result, carry, overflow, ins.setflags)
    
    def emulate_sub_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            if len(ins.operands) == 3:
                Rd, Rn, Rm = ins.operands
                shift_t = SRType_LSL
                shift_n = 0
                
            else:
                Rd, Rn, Rm, shift = ins.operands
                shift_t = shift.type_
                shift_n = shift.value

            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(R[n], NOT(shifted), '1');
            Rn_val = self.getRegister(Rn)
            result, carry, overflow = AddWithCarry(Rn_val, NOT(shifted), 1)            
            self.__write_reg_and_set_flags__(Rd, result, carry, overflow, ins.setflags)                
            
    
    def emulate_sub_rsr(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
                        
            # shift_n = UInt(R[s]<7:0>);
            shift_n = get_bits(self.getRegister(shift.value), 7, 0)
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(R[n], NOT(shifted), '1');
            result, carry, overflow = AddWithCarry(self.getRegister(Rn), NOT(shifted), 1)
            
            self.__write_reg_and_set_flags__(Rn, result, carry, overflow, ins.setflags)
    
    def emulate_sub_sp_minus_immediate(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rd, Rn, imm32 = ins.operands
            
            # (result, carry, overflow) = AddWithCarry(SP, NOT(imm32), '1');
            result, carry, overflow = AddWithCarry(self.getRegister(Rn), NOT(imm32.n), '1');
            
            self.__write_reg_and_set_flags__(Rd, result, carry, overflow, ins.setflags)
    
    def emulate_sub_sp_minus_register(self, ins):
        """
        Done
        """
        if self.ConditionPassed(ins):
            Rd, Rn, Rm, shift = ins.operands
            shift_t = shift.type_
            shift_n = shift.value
            
            # shifted = Shift(R[m], shift_t, shift_n, APSR.C);
            shifted = Shift(self.getRegister(Rm), shift_t, shift_n, self.getCarryFlag())
            
            # (result, carry, overflow) = AddWithCarry(SP, NOT(shifted), '1');
            result, carry, overflow = AddWithCarry(self.getRegister(Rn), NOT(shifted), 1)
            
            self.__write_reg_and_set_flags__(Rd, result, carry, overflow, ins.setflags)

    def emulate_subs_pc_lr_arm(self, ins):
        """
        TODO:
        """
        if self.ConditionPassed(ins):
            raise NotImplementedError()
    
    def emulate_subs_pc_lr_thumb(self, ins):
        """
        TODO:
        Half-Done: We need to get the value of SPSR regiter.
        """
        if self.ConditionPassed(ins):
            Rd, Rn, imm32 = ins.operands
    
            # TODO: add  or self.CurrentInstrSet() == InstrSet_ThumbEE
            if self.CurrentModeIsUserOrSystem():
                raise UnpredictableInstructionException()
            else:
                operand2 = imm32.n
                
                # (result, -, -) = AddWithCarry(R[n], NOT(operand2), '1');
                result, carry, overflow = AddWithCarry(self.getRegister(Rn), NOT(operand2), 1)
                
                # TODO: Get the "Saved Program Status Register (SPSR)"
                # CPSRWriteByInstr(SPSR[], '1111', TRUE);
                # self.CPSRWriteByInstr(data, 0b1111, True)
                #
                # if CPSR<4:0> == '11010' && CPSR.J == '1' && CPSR.T == '1' then
                #     UNPREDICTABLE
                # else
                #     BranchWritePC(result);
    
    def emulate_svc(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_swp(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_teq_immediate(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_teq_register(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_teq_rsr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_thumb(self, opcode):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_tst_immediate(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_tst_register(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_tst_rsr(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_umaal(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_umlal(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_umull(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_unknown(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_wfe(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_wfi(self, ins):
        if self.ConditionPassed(ins):
            pass
    
    def emulate_yield(self, ins):
        if self.ConditionPassed(ins):
            pass

    def emulate(self, ins, dump_state=False):
        """
        Emulate an instruction, optionally dumping the state of
        the processor prior and post execution of the instruction.
        """
        if dump_state:
            print self.dump_state()
            print ins
        
        if ins.id == ARMInstruction.adc_immediate:
            self.emulate_adc_immediate(ins)
        
        elif ins.id == ARMInstruction.adc_register:
            self.emulate_adc_register(ins)
            
        elif ins.id == ARMInstruction.adc_rsr:
            self.emulate_adc_rsr(ins)
            
        else:
            raise InstructionNotImplementedException()

        if dump_state:
            print self.dump_state()
            print
        
    def dump_state(self):
        """
        Return a string representation of the emulator state.
        """
        regs = []
        for i in xrange(0, 16):
            r = Register(i)
            v = self.getRegister(r)
            if v:
                regs.append("%s=%x" % (r, v))
            
        flags = []
        flags.append("%s=%d" % ("C", self.getFlag(ARMFLag.C)))
        flags.append("%s=%d" % ("N", self.getFlag(ARMFLag.N)))
        flags.append("%s=%d" % ("V", self.getFlag(ARMFLag.V)))
        flags.append("%s=%d" % ("Z", self.getFlag(ARMFLag.Z)))
        
        return "Flags: [%s] - Registers: [%s]" % (", ".join(flags), ", ".join(regs))

if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    
    memory_map = DummyMemoryMap() 
    emulator = ARMEmulator(memory_map)
         
    ins = Instruction("ADC", True, None, [Register(ARMRegister.R0), Register(ARMRegister.R1), Register(ARMRegister.R2), RegisterShift(SRType_ASR, 4)], eEncodingA2)
    ins.id = ARMInstruction.adc_register
    emulator.emulate(ins, dump_state=True)
