from disassembler.constants.arm import ARMEncodings
from disassembler.utils.bits import get_bit

class Instruction(object):
    def __init__(self, id_, opcode, name, setflags, condition, operands, encoding, qualifiers=""):
        self.id = id_
        self.opcode = opcode
        self.name = name
        self.setflags = setflags

        self.thumb32 = False

        if condition:
            self.condition = condition
        else:
            self.condition = ""
            
        self.qualifiers = qualifiers
        self.operands = operands
        self.encoding = encoding

        # ???
        self.effects = []

    def mode(self):
        if self.encoding in ARMEncodings:
            return ARMMode.ARM

        return ARMMode.THUMB

    def __str__(self):
        if self.setflags:
            sf = "S"
        else:
            sf = ""
        
        buffer_ = "%s%s%s%s " % (self.name, sf, self.condition, self.qualifiers.replace(".", ""))
        buffer_ += ", ".join([x for x in map(str, self.operands) if x != ""])
        
        return buffer_

class InvalidInstructionEncoding(Exception):
    def __init__(self, message=""):
        self.message = message

    def __str__(self):
        return "Invalid encoding for instruction: %s" % self.message

class InvalidModeException(Exception):
    pass

class UnpredictableInstructionException(Exception):
    def __init__(self, message=""):
        self.message = message
        
    def __str__(self):
        return "Unpredictable instruction: %s" % self.message

class InstructionNotImplementedException(Exception):
    def __init__(self, message=""):
        self.message = message
        
    def __str__(self):
        return "Instruction not implemented: %s" % self.message

class BreakpointDebugEvent(Exception):
    def __init__(self, message=""):
        self.message = message

    def __str__(self):
        return "Breakpoint event: %s" % self.message

class HintDebug(Exception):
    def __init__(self, message=""):
        self.message = message

    def __str__(self):
        return "Hint Debug: %s" % self.message

class RegisterShift(object):
    def __init__(self, shift_t, shift_n):
        self.type_ = shift_t
        
        # shift_n could be a number or a register
        if type(shift_n) in [int, long]:
            self.value = Immediate(shift_n)
        else:
            self.value = shift_n

    def __str__(self):
        if type(self.value) == Immediate and self.value.n == 0:
            return ""
        
        if type(self.value) in [int, long]:
            val = "#%d" % self.value
        else:
            val = "%r" % self.value
        
        if self.type_ == 0:
            return "lsl %s" % (val)
        elif self.type_ == 1:
            return "lsr %s" % (val)
        elif self.type_ == 2:
            return "asr %s" % (val)
        elif self.type_ == 3:
            return "ror %s" % (val)
        elif self.type_ == 4:
            if val == "#1":
                return "rrx"
            
            return "rrx %s" % (val)
        else:
            return "INV"

class RegisterSet(object):
    def __init__(self, registers):
        self.registers = registers
        self.repr = None
    
    def __str__(self):
        if self.repr:
            return self.repr
        
        t = []
        for i in xrange(0, 15 + 1):
            if get_bit(self.registers, i):
                t.append(Register(i))
                
        self.repr = "{" + ", ".join(map(lambda x: str(x), t)) + "}"
        return self.repr 

class ProcessorFlag(object):
    def __init__(self, flag):
        self.flag = flag
        
    def __str__(self):
        if self.flag == 0:
            return "N"
        elif self.flag == 1:
            return "Z"
        elif self.flag == 2:
            return "C"
        elif self.flag == 3:
            return "V"
        elif self.flag == 4:
            return "Q"   

class Register(object):
    def __init__(self, reg, wback=False, negative=False):
        self.reg = reg
        if wback:
            self.wback = True
        else:
            self.wback = False
            
        self.negative = negative

    def __str__(self):
        if self.reg == 13:
            t = "sp"
        elif self.reg == 14:
            t = "lr"
        elif self.reg == 15:
            t = "pc"
        elif self.reg == 10:
            t = "sl"
        elif self.reg == 11:
            t = "fp"
        elif self.reg == 12:
            t = "ip"
        else:
            t = "r%d" % self.reg

        if self.wback:
            t += "!"

        if self.negative:
            t = "-" + t
        
        return t
    
    def __eq__(self, other):
        if isinstance(other, Register):
            return self.reg == other.reg
        else:
            return self.reg == other
    
    def __repr__(self):
        return self.__str__()

class Memory(object):
    def __init__(self, op1=None, op2=None, op3=None, wback=False):
        self.op1 = op1
        self.op2 = op2
        self.op3 = op3
        self.wback = wback

    def __str__(self):
        ret = ""
        if self.op1:
            if self.op2:
                if self.op3 and len(str(self.op3)):
                    ret = "[%s, %s, %s]" % (self.op1, self.op2, self.op3)
                else:
                    ret = "[%s, %s]" % (self.op1, self.op2)
            else:
                if self.op3 and len(str(self.op3)):
                    ret = "[%s, %s]" % (self.op1, self.op3)
                else:
                    ret = "[%s]" % (self.op1)
        
        if self.wback:
            ret += "!"
            
        return ret

class Immediate(object):
    def __init__(self, n):
        self.n = n

    def __str__(self):
        return "#{:#d}".format(self.n)

    def __repr__(self):
        return self.__str__()

    def __bool__(self):
        return bool(self.n)

class Jump(object):
    def __init__(self, addr):
        if addr & 0x80000000:
            addr = -0x100000000 + addr
        self.addr = addr

    def __str__(self):
        return "#%d" % self.addr

class UndefinedOpcode(Exception):
    def __init__(self, word=0):
        self.word = word

    def __str__(self):
        return "<undefined opcode>"

class Condition(object):
    """
    Verified
    """
    def __init__(self, cond):
        self.cond = cond        

        if self.cond == 0b0000:
            self.name = "EQ"
            self.explain = "Z == 1"
            self.meaning = "Equal"
        elif self.cond == 0b0001:
            self.name = "NE"
            self.explain = "Z == 0"
            self.meaning = "Not equal"
        elif self.cond == 0b0010:
            self.name = "CS"
            self.explain = "C == 1"
            self.meaning = "Carry set"
        elif self.cond == 0b0011:
            self.name = "CC"
            self.explain = "C == 0"
            self.meaning = "Carry clear"
        elif self.cond == 0b0100:
            self.name = "MI"
            self.explain = "N == 1"
            self.meaning = "Minus, negative"
        elif self.cond == 0b0101:
            self.name = "PL"
            self.explain = "N == 0"
            self.meaning = "Plus, positive or zero"
        elif self.cond == 0b0110:
            self.name = "VS"
            self.explain = "V == 1"
            self.meaning = "Overflow"
        elif self.cond == 0b0111:
            self.name = "VC"
            self.explain = "V == 0"
            self.meaning = "No overflow"
        elif self.cond == 0b1000:
            self.name = "HI"
            self.explain = "C == 1 and Z == 0"
            self.meaning = "Unsigned higher"
        elif self.cond == 0b1001:
            self.name = "LS"
            self.explain = "C == 0 or  Z == 1"
            self.meaning = "Unsigned lower or same"
        elif self.cond == 0b1010:
            self.name = "GE"
            self.explain = "N == V"
            self.meaning = "Signed greater than or equal"
        elif self.cond == 0b1011:
            self.name = "LT"
            self.explain = "N != V"
            self.meaning = "Signed less than"
        elif self.cond == 0b1100:
            self.name = "GT"
            self.explain = "Z == 0 and N == V"
            self.meaning = "Signed greater than"
        elif self.cond == 0b1101:
            self.name = "LE"
            self.explain = "Z == 1 or N != V"
            self.meaning = "Signed less than or equal"
        elif self.cond == 0b1110:
            self.name = ""
            self.explain = "Any"
            self.meaning = "Always"
        else:
            self.name = ""
            self.explain = "Invalid"
            self.meaning = "Invalid"

    def __str__(self):
        return self.name

flag2string = {}
flag2string[0] = "N"
flag2string[1] = "Z"
flag2string[2] = "C"
flag2string[3] = "V"
flag2string[4] = "Q"

class Flag(object):
    def __init__(self, flag):
        self.flag = flag
        self.bit_pos = 31 - flag
        
    def __str__(self):
        return flag2string[self.flag]

    def __eq__(self, other):
        if isinstance(other, Flag):
            return self.flag == other.flag
        else:
            return self.flag == other
    
    def __repr__(self):
        return self.__str__()
    
class ARMFLag:
    N = Flag(0)
    Z = Flag(1)
    C = Flag(2)
    V = Flag(3)
    Q = Flag(4)



class ARMMode:
    THUMB = 0
    ARM = 1
    JAZELLE = 2
    THUMBEE = 3

class ARMRegister:
    """
    ARM core registers
    """
    R0 = Register(0)
    R1 = Register(1)
    R2 = Register(2)
    R3 = Register(3)
    R4 = Register(4)
    R5 = Register(5)
    R6 = Register(6)
    R7 = Register(7)
    R8 = Register(8)
    R9 = Register(9)
    R10 = SL = Register(10)
    R11 = FP = Register(11)
    R12 = IP = Register(12)
    R13 = SP = Register(13)
    R14 = LR = Register(14)
    R15 = PC = Register(15)
