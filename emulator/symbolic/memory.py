'''
Created on Jul 25, 2013

@author: pablo


'''

from emulator.memory import ConcreteMemoryMap
from emulator.symbolic.expression import BvExpr, BvExtractExpr, BvConcatExpr, BvConstExpr
from collections import deque

class DeferredMemRead(BvExpr):
    __sort__="BitVec 8"
    size=8
    size_mask=255
    def __init__(self, address, generation):
        self.address=address
        self.generation=generation
    
    def __str__(self):
        if not isinstance(self.address, BvExpr) or self.address.__has_value__:
            return "memread(0x%x)" % self.address
        else:
            return "memread(%s)" % self.address

class AbstractMemoryMap(ConcreteMemoryMap):
    def __init__(self):
        ConcreteMemoryMap.__init__(self)
        self.stored_since_last_read = False
        self.generation = 0
        
    def __setitem__(self, address, value):
        self.stored_since_last_read = True
        if not self.memory.has_key(address):
            self.memory[address] = deque()
            self.memory[address].append((value, self.generation))
        else:
            lastgen = self.memory[address][-1][1]
            if lastgen == self.generation: #replace latest value
                self.memory[address][-1]=(value, lastgen)
            else:
                self.memory[address].append((value, self.generation))
                
    def __getitem__(self, address):
        if self.memory.has_key(address):
            return self.memory[address][-1][0]
        else:
            ret = DeferredMemRead(address, self.generation) 
            if self.stored_since_last_read:
                self.stored_since_last_read = False
                self.generation += 1

            return ret

    def __split_bytes_le__(self, value, size):
        if size == 1:
            return [value] if not isinstance(value, BvExpr) else [value & 0xff]

        out=[]
        if not isinstance(value, BvExpr) or value.__has_value__:
            for _ in range(size):
                out.append(value & 0xff)
                value >>= 8
        else:
            for x in range(size):
                out.append(BvExtractExpr(value, ((x + 1) * 8) - 1, x * 8))
        return out
    
    def __join_bytes_le__(self, values):
        #try to join native numeral subexpressions first
        newvalues=[]
        to_join=0
        for x in range(0, len(values)):
            if not isinstance(values[x], BvExpr) or values[x].__has_value__:
                to_join+=1
                continue
            elif to_join:
                #use the ConcreteMemoryMap join function for sub-lists of values
                newvalues.append((ConcreteMemoryMap.__join_bytes_le__(self, values[x - to_join:x]), to_join))
                to_join=0
                
            newvalues.append((values[x], 1))
                
        if to_join:
            newvalues.append((ConcreteMemoryMap.__join_bytes_le__(self, values[x - to_join + 1:x + 1]), to_join))
        
        (val, size) = newvalues[0]
        for x in range(1, len(newvalues)):
            if not isinstance(val, BvExpr):
                val = BvConstExpr(val, size * 8)
            if isinstance(newvalues[x][0], BvExpr):
                second = newvalues[x][0]
            else:
                second = BvConstExpr(newvalues[x][0], newvalues[x][1] * 8)
            val = BvConcatExpr(second, val)
        return val
