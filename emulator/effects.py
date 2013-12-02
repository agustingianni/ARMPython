'''
Created on Nov 30, 2013

@author: anon
'''

class InstructionEffect(object):
    def __init__(self):
        self.type_ = "UNKNOWN"

class ReadEffect(InstructionEffect):
    def __init__(self, what, value):
        super(ReadEffect, self).__init__()
        
        self.what = what
        self.value = value

    def __str__(self):
        return "%16s: %14s | 0x%.8x" % (self.type_, self.what, self.value)

class WriteEffect(InstructionEffect):
    def __init__(self, what, value, old_value):
        super(WriteEffect, self).__init__()
        
        self.what = what
        self.value = value
        self.old_value = old_value

    def __str__(self):
        return "%16s: %14s | 0x%.8x -> 0x%.8x" % (self.type_, self.what, self.old_value, self.value)

class MemoryReadEffect(ReadEffect):
    def __init__(self, address, value):
        super(MemoryReadEffect, self).__init__("[0x%.8x]" % address, value)
        self.type_ = "MemoryRead"

class MemoryWriteEffect(WriteEffect):
    def __init__(self, address, value, old_value):
        super(MemoryWriteEffect, self).__init__("[0x%.8x]" % address, value, old_value)
        self.type_ = "MemoryWrite"

class RegisterReadEffect(ReadEffect):
    def __init__(self, register, value):
        super(RegisterReadEffect, self).__init__(register, value)
        self.type_ = "RegisterRead"

class RegisterWriteEffect(WriteEffect):
    def __init__(self, register, value, old_value):
        super(RegisterWriteEffect, self).__init__(register, value, old_value)
        self.type_ = "RegisterWrite"
        
class FlagReadEffect(ReadEffect):
    def __init__(self, flag, value):
        super(FlagReadEffect, self).__init__(flag, value)
        self.type_ = "FlagRead"

class FlagWriteEffect(WriteEffect):
    def __init__(self, flag, value, old_value):
        super(FlagWriteEffect, self).__init__(flag, value, old_value)
        self.type_ = "FlagWrite"
