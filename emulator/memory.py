'''
Created on Jun 12, 2013

@author: anon
'''
class MemoryMap(object):
    def __init__(self):
        pass
        
    def __getitem__(self, address):
        raise Exception("Method not implemented.")
    
    def __setitem__(self, address, value):
        raise Exception("Method not implemented.")
    
    def __set_bytes__(self, address, value, size):
        raise Exception("Method not implemented.")
    
    def __get_bytes__(self, address, size):
        raise Exception("Method not implemented.")
    
    def set_byte(self, address, value):
        self.__set_bytes__(address, value, 1)
    
    def set_word(self, address, value):
        self.__set_bytes__(address, value, 2)
    
    def set_dword(self, address, value):
        self.__set_bytes__(address, value, 4)

    def get_byte(self, address):
        return self.__get_bytes__(address, 1)
    
    def get_word(self, address):
        return self.__get_bytes__(address, 2)
    
    def get_dword(self, address):
        return self.__get_bytes__(address, 4)

class ConcreteMemoryMap(MemoryMap):
    def __init__(self):
        MemoryMap.__init__(self)
        self.memory = {}
        
    def __setitem__(self, address, value):
        self.memory[address] = value
                
    def __getitem__(self, address):
        return self.memory[address]

    def __set_bytes__(self, address, value, size):
        for i in xrange(0, size):
            #print "[%.8x]  = %.2x" % (address + i, ord(value[i]))
            self.__setitem__(address + i, ord(value[i]))
    
    def __get_bytes__(self, address, size):
        values = []
        for i in xrange(0, size):
            values.append(self.__getitem__(address + i))
        
        # Concatenate the bytes
        val = values[0]
        for x in xrange(1, size):
            val |= values[x] << (8 * x)        
        
        return val

class DummyMemoryMap(ConcreteMemoryMap):
    """
    A dummy memory map is a test map that will return an incremental value.
    """
    def __init__(self):
        ConcreteMemoryMap.__init__(self)
        self.value = 0

    def __getitem__(self, address):
        self.value += 1
        return self.value & 0xff