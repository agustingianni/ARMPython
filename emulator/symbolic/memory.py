'''
Created on Jul 25, 2013

@author: pablo


'''

from emulator.memory import ConcreteMemoryMap, MemoryMap
from emulator.symbolic.bitvector_expr import BvExpr, BvConstExpr
from emulator.symbolic.base_expr import ExportParameters
from collections import OrderedDict

class DeferredMemRead(BvExpr):
    __slots__=("memmap", "generation")
    __sort__="(_ BitVec 8)"
    size=8
    size_mask=255
    __depth__=1
    __backend_fun__=lambda: None
    def __init__(self, address, memmap):
        self.children=(address, )
        self.memmap=memmap
        self.generation=memmap.generation
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    def __str__(self):
        return "memread(%s)" % self.children[0]
    
    def __export__(self):
        return "(select mem_%d %s)" % (self.generation, self.children[0].export())
    
    @staticmethod
    def construct(address, memmap, addr_size):
        if not isinstance(address, BvExpr):
            address = BvConstExpr.construct(address, addr_size)
        return DeferredMemRead(address, memmap)

class AbstractMemoryMap(ConcreteMemoryMap):
    memory = OrderedDict()
    sentinel = object()
    commited_memory = []
    stored_since_last_read = False
    generation = 0

    def __init__(self, address_size=32):
        MemoryMap.__init__(self)
        self.address_size = address_size
        self.memory[self.sentinel] = self.sentinel
        
    def __setitem__(self, address, value):
        self.stored_since_last_read = True
        if address in self.memory:
            #we need to re-create the entry to affect the order
            del self.memory[address]

        self.memory[address] = value
    
    def __getitem__(self, address):
        if self.memory.has_key(address):
            return self.memory[address]
        else:
            if self.stored_since_last_read:
                self.commitMemArray()

            ret = DeferredMemRead.construct(address, self, self.address_size)

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
                out.append(value.extract(((x + 1) * 8) - 1, x * 8))
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
                val = BvConstExpr.construct(val, size * 8)
            if isinstance(newvalues[x][0], BvExpr):
                second = newvalues[x][0]
            else:
                second = BvConstExpr.construct(newvalues[x][0], newvalues[x][1] * 8)
            val = second.concat(val)
        return val

    def commitMemArray(self):
        #local accessors for extra-speed
        mem = self.memory
        cmem = []
        senti = self.sentinel

        for address in reversed(mem):
            #if we reach the sentinel it means we already commited the rest
            if id(senti) == id(address):
                #move the sentinel to the end
                del mem[senti]
                mem[senti]=senti
                break
            
            #this list has the memory writes reversed! (first item is last operation)
            cmem.append( (address, mem[address]) )
        
        self.executeMemCommit(self.generation, cmem)
    
    #this function must be overloaded by each solver implementation
    def executeMemCommit(self, gen, changes):
        self.commited_memory.append( (gen, changes) ) 

    def export(self):
        def __helper(addr, val):
            if isinstance(addr, BvExpr):
                addr = addr.export()
            else:
                #taken from BvConstExpr __export__ function
                addr = ("#x%0" + str(((self.address_size - 1) // 4) + 1) + "x") % addr
            
            if isinstance(val, BvExpr):
                val = val.export()
            else:
                val = "#x%02x" % val
            return (addr, val)

        if self.stored_since_last_read:
            self.commitMemArray()

        ExportParameters().declares["mem"] = "(declare-const mem (Array (_ BitVec %d) (_ BitVec 8)))" % self.address_size

        if not len(self.commited_memory):
            ExportParameters().declares["mem_0"] = "(declare-const mem_0 (Array (_ BitVec %d) (_ BitVec 8)))\n" % self.address_size
            ExportParameters().asserts.append("(= mem_0 mem)")
        else:
            prev="mem"
            for gen, cmem in self.commited_memory:
                ExportParameters().declares["mem_%d" % gen] = "(declare-const mem_%d (Array (_ BitVec %d) (_ BitVec 8)))\n" % (gen, self.address_size)
                
                ret = ""
                if not len(cmem):
                    ret += prev
                else:
                    ret += "(store" * len(cmem)
                    addr,val = __helper(*cmem.pop(0))
                    ret += " %s %s %s)" % (prev, addr, val)
                    for addr, val in cmem:
                        addr,val = __helper(addr, val)
                        ret += " %s %s)" % (addr, val)
                    prev = "mem_%d" % gen
                
                ExportParameters().asserts.append("(= mem_%d %s)" % (gen, ret))
