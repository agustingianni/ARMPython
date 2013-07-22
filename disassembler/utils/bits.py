'''
Created on Jun 12, 2013

@author: anon
'''
def get_bits(value, end, start):
    return (value >> start) & ((1 << (end - start + 1)) - 1)

def get_bit(value, bit):
    return ((value >> bit) & 1)

def Align(val, alignment):
    return alignment * (val / alignment)

# If x is a bitstring, SInt(x) is the integer whose two's complement representation is x
def SInt(x, N):
    result = 0
    for i in xrange(0, N):
        if get_bit(x, i):
            result = result + 2 ** i
    
    if get_bit(x, N-1):
        result = result - 2 ** N
        
    return result

# UInt(x) is the integer whose unsigned representation is x:
def UInt(x, N):
    result = 0
    for i in xrange(0, N):
        if get_bit(x, i):
            result = result + 2 ** i    

    return result

def SignExtend32(number, bits):
    if number & (1 << (bits - 1)):
        mask = (1 << (32 - bits)) - 1
        mask = mask << bits
        return number | mask
    
    return number

def SignExtend64(number, bits):
    if number & (1 << (bits - 1)):
        mask = (1 << (64 - bits)) - 1
        mask = mask << bits
        return number | mask
    
    return number

def CountLeadingZeroBits(n):
    i = 31
    c = 0
    while i > 0:
        if get_bit(n, i):
            break
        i -= 1
        c += 1
        
    return c

def LowestSetBit(n):
    bit = 32
    for i in xrange(0, 32):
        if get_bit(n, i):
            bit = i
            break
        
    return bit
    

def CountTrailingZeros(n):
    if not n:
        return 0
    
    t = 0
    while not n & 1:
        n >>= 1
        t += 1
    
    return t

def BitCount(x):
    c = 0
    while x != 0:
        c += 1
        x &= x - 1
    
    return c

def ror(val, N, shift):
    m = shift % N;
    return ((val >> m) | (val << (N - m))) & (2 ** N - 1)
