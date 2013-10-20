'''
Created on Jun 12, 2013

@author: anon
'''


def GetLastValidAddress(memory_map):
    keys = memory_map.memory.keys()
    if not len(keys):
        return 0

    return max(keys)


def GetNextValidAddress(memory_map, address):
    # TODO: This is slow.
    for e in sorted(memory_map.memory.keys()):
        if e >= address:
            return e

    return None


class MemoryMapIterator(object):
    def __init__(self, mem_map, start_addr=None, end_addr=None, step_size=4):
        self.memory = mem_map
        self.end_addr = end_addr
        self.step_size = step_size

        if start_addr is None:
            self.curr_addr = 0

        else:
            self.curr_addr = start_addr


    def __iter__(self):
        return self

    def next(self):
        # Get the next valid address starting from the current address.
        self.curr_addr = GetNextValidAddress(self.memory, self.curr_addr)

        if self.curr_addr is None or (self.curr_addr >= self.end_addr and self.end_addr is not None):
            raise StopIteration

        if self.step_size == 1:
            el = self.memory.get_byte(self.curr_addr)

        elif self.step_size == 2:
            el = self.memory.get_word(self.curr_addr)

        elif self.step_size == 4:
            el = self.memory.get_dword(self.curr_addr)

        elif self.step_size == 8:
            el = self.memory.get_qword(self.curr_addr)

        else:
            raise Exception("Invalid step size")

        addr = self.curr_addr
        self.curr_addr += self.step_size

        return addr, el


class MemoryMap(object):
    LittleEndianMode = 0
    BigEndianMode = 1

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

    def is_mapped(self, address):
        return self.__getitem__(address) is not None

    def __getitem__(self, address):
        """
        Should return None for unmapped addresses. Avoid using exceptions due to performance.
        """
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

    def memset(self, address, value, size):
        for i in xrange(0, size):
            self.set_byte(address + i, value & 0xff)

    def get_byte(self, address):
        return self.__join_bytes__(self.__get_bytes__(address, 1))

    def get_word(self, address):
        return self.__join_bytes__(self.__get_bytes__(address, 2))

    def get_dword(self, address):
        return self.__join_bytes__(self.__get_bytes__(address, 4))

    def get_qword(self, address):
        return self.__join_bytes__(self.__get_bytes__(address, 8))

    def get_bytes(self, address, size):
        out = ""
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
        if self.memory.has_key(address):
            return self.memory[address]

        return None

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
        out = []
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
        out = self.__split_bytes_le__(value, size)
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
        return 0


def main():
    mem_map = ConcreteMemoryMap()
    mem_map.set_dword(0xcafecafe, 0xdeadbeef)
    mem_map.set_dword(0xdeadbeef, 0xcafecafe)
    for addr, value in MemoryMapIterator(mem_map, step_size=1):
        print "ADDR = %.8x | VAL = %.8x" % (addr, value)


if __name__ == "__main__":
    main()