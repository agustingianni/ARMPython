'''
Created on Jun 12, 2013

@author: anon
'''

class MemoryMap(object):
    LittleEndianMode=0
    BigEndianMode=1

    def __init__(self, mode=LittleEndianMode):
        self.mode = mode
        self.setMode(mode)
    
    def setMode(self, mode):
        if mode == MemoryMap.LittleEndianMode:
            self.__split_bytes__ = self.__split_bytes_le__
            self.__join_bytes__ = self.__join_bytes_le__
        else:
            self.__split_bytes__ = self.__split_bytes_be__
            self.__join_bytes__ = self.__join_bytes_be__
        
    def __getitem__(self, address):
        raise Exception("Method not implemented.")
    
    def __setitem__(self, address, value):
        raise Exception("Method not implemented.")
    
    def __set_bytes__(self, address, value):
        """
        Receives an iterable of byte values.
        All byte values are already inside the boundaries of a 8-bits byte.
        """
        raise Exception("Method not implemented.")
    
    def __get_bytes__(self, address, size):
        raise Exception("Method not implemented.")
    
    def __split_bytes_le__(self, value, size):
        raise Exception("Method not implemented.")

    def __join_bytes_le__(self, value, size):
        raise Exception("Method not implemented.")

    def __split_bytes_be__(self, value, size):
        raise Exception("Method not implemented.")

    def __join_bytes_be__(self, value, size):
        raise Exception("Method not implemented.")
    
    def set_byte(self, address, value):
        self.__set_bytes__(address, self.__split_bytes__(value, 1))
    
    def set_word(self, address, value):
        self.__set_bytes__(address, self.__split_bytes__(value, 2))
    
    def set_dword(self, address, value):
        self.__set_bytes__(address, self.__split_bytes__(value, 4))

    def set_qword(self, address, value):
        self.__set_bytes__(address, self.__split_bytes__(value, 8))
    
    def set_bytes(self, address, chars):
        for i in range(len(chars)):
            self.set_byte(address + i, ord(chars[i]))

    def get_byte(self, address):
        return self.__join_bytes__(self.__get_bytes__(address, 1))
    
    def get_word(self, address):
        return self.__join_bytes__(self.__get_bytes__(address, 2))
    
    def get_dword(self, address):
        return self.__join_bytes__(self.__get_bytes__(address, 4))
    
    def get_qword(self, address):
        return self.__join_bytes__(self.__get_bytes__(address, 8))
    
    def get_bytes(self, address, size):
        out=""
        for ch in self.__get_bytes__(address, size):
            out += chr(ch)
        return out

class ConcreteMemoryMap(MemoryMap):
    def __init__(self):
        MemoryMap.__init__(self)
        self.memory = {}
        
    def __setitem__(self, address, value):
        self.memory[address] = value & 0xff
                
    def __getitem__(self, address):
        return self.memory[address]

    def __set_bytes__(self, address, value):
        for i in range(len(value)):
            #print "[%.8x]  = %.2x" % (address + i, value[i])
            self.__setitem__(address + i, value[i])
    
    def __get_bytes__(self, address, size):
        values = []
        for i in xrange(0, size):
            values.append(self.__getitem__(address + i))
        
        return values
    
    def __split_bytes_le__(self, value, size):
        out=[]
        for _ in range(size):
            out.append(value & 0xff)
            value >>= 8
        return out
    
    def __join_bytes_le__(self, values):
        val = values[0]
        for x in range(1, len(values)):
            val |= values[x] << (8 * x)
        return val
    
    def __split_bytes_be__(self, value, size):
        out=self.__split_bytes_le__(value, size)
        out.reverse()
        return out

    def __join_bytes_be__(self, values):
        values.reverse()
        return self.__join_bytes_le__(values)
        

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

class NullMemoryMap(ConcreteMemoryMap):
    """
    Returns always 0
    """
    def __init__(self):
        ConcreteMemoryMap.__init__(self)

    def __getitem__(self, address):
        self.value += 1
        return 0
