'''
Created on Jun 12, 2013

@author: anon
'''

def Align(val, alignment):
    return alignment * (val / alignment)

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

def countTrailingZeros(n):
    if not n:
        return 0
    
    t = 0
    while not n & 1:
        n >>= 1
        t += 1
    
    return t

def get_bits(value, end, start):
    return (value >> start) & ((1 << (end - start + 1)) - 1)

def get_bit(value, bit):
    return ((value >> bit) & 1)

def BitCount(x):
    c = 0
    while x != 0:
        c += 1
        x &= x - 1
    
    return c

def ror(val, N, shift):
    m = shift % N;
    return ((val >> m) | (val << (N - m))) & (2 ** N - 1)
