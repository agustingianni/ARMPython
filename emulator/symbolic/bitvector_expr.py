from emulator.symbolic.base_expr import Expr
from emulator.symbolic.boolean_expr import EqExpr, DistinctExpr, BoolExpr, TrueExpr, FalseExpr
from utils.lru import LruCache
import math

class BvExpr(Expr):
    __base_sort__="BitVec"
    
    @classmethod
    def __associative_construct__(cls, p1, p2, force_assoc=True):
        #float constants to the right
        if isinstance(p1, BvConstExpr):
            tmp = p2
            p2 = p1
            p1 = tmp
    
        #Force associativity to the right
        #(a * b) * c   <=>   a * (b * c)
        #   p1     p2
        if force_assoc and isinstance(p1, cls):
            p2 = cls.__python_op__(p1.children[1], p2) #b * c
            p1 = p1.children[0] #a
        
        return p1, p2
    
    def __nonzero__(self):
        raise Exception, "A BitVector Expression cannot be evaluated to boolean"
    
    def __len__(self):
        return self.size

    def __and__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvAndExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return value & secondary
            else:
                #p & 0 = 0
                if value == 0:
                    return 0
                
                #p & all-1 = p
                if value == self.size_mask:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvAndExpr.construct(self, other)

    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvOrExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value | secondary) & self.size_mask
            else:
                #p | 0 = p
                if value == 0:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask
                
                #p | all-1 = all-1
                if value == self.size_mask:
                    return self.size_mask

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvOrExpr.construct(self, other)

    def __ror__(self, other):
        return self.__or__(other)
    
    def __xor__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvXorExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value ^ secondary) & self.size_mask
            else:
                #p ^ 0 = p
                if value == 0:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask
                
                #p ^ all-1 = ~p
                if value == self.size_mask:
                    return ~secondary if isinstance(secondary, BvExpr) else (~secondary) & self.size_mask

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvXorExpr.construct(self, other)

    def __rxor__(self, other):
        return self.__xor__(other)
    
    def __invert__(self):
        if self.__has_value__:
            return (~self.value) & self.size_mask
        else:
            return BvNotExpr.construct(self)
    
    def __neg__(self):
        if self.__has_value__:
            return (-self.value) & self.size_mask
        else:
            return BvNegExpr.construct(self)
    
    def __rshift__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvShrExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or other.__has_value__):
                return self.value >> long(other)
            else:
                if not self.__has_value__:
                    other_value=long(other)
                    
                    #p >> 0 = p
                    if other_value == 0:
                        return self
                    
                    #p >> size(p) = 0
                    if other_value >= self.size:
                        return 0
                    
                    #(a >> n) >> m == a >> n+m
                    if isinstance(self, BvShrExpr):
                        return self.children[0] >> ((self.children[1] % _next_power_of_two(self.size)) + other_value)

                    if not other_is_expr:
                        other = BvConstExpr.construct(other_value, self.size)
                
                # 0 >> p = 0
                elif self.value == 0:
                    return 0

                return BvShrExpr.construct(self, other)

    def __rrshift__(self, other):
        if self.__has_value__:
            return (other >> self.value) & self.size_mask
        else:
            # 0 >> p = 0
            if other == 0:
                return 0
            return BvShrExpr.construct(BvConstExpr.construct(other, self.size), self)
    
    def __lshift__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvShlExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or other.__has_value__):
                return (self.value << long(other)) & self.size_mask
            else:
                if not self.__has_value__:
                    other_value=long(other)

                    #p << 0 = p
                    if other_value == 0:
                        return self
                    
                    #p << size(p) = 0
                    if other_value >= self.size:
                        return 0

                    #(a >> n) >> m == a >> n+m
                    if isinstance(self, BvShlExpr):
                        return self.children[0] << ((self.children[1] % _next_power_of_two(self.size)) + other_value)
                    
                    if not other_is_expr:
                        other = BvConstExpr.construct(other_value, self.size)
                
                # 0 << p = 0
                elif self.value == 0:
                    return 0

                return BvShlExpr.construct(self, other)

    def __rlshift__(self, other):
        if self.__has_value__:
            return (other << self.value) & self.size_mask
        else:
            # 0 << p = 0
            if other == 0:
                return 0
            return BvShlExpr.construct(BvConstExpr.construct(other, self.size), self)

    def __add__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvAddExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value + secondary) & self.size_mask
            else:
                #p + 0 = p
                if value == 0:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask
                
                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvAddExpr.construct(self, other)

    def __radd__(self, other):
        return self.__add__(other)

    def __sub__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvSubExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or other.__has_value__):
                return (self.value - long(other)) & self.size_mask
            else:
                #p - 0 = p
                if not self.__has_value__ and long(other) == 0:
                    return self
                
                #0 - p = -p
                if self.__has_value__ and self.value == 0:
                    return -other if other_is_expr else (-other) & self.size_mask

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvSubExpr.construct(self, other)

    def __rsub__(self, other):
        if self.__has_value__:
            return (other - self.value) & self.size_mask
        else:
            #0 - p = -p
            if other == 0:
                return -self

            return BvSubExpr.construct(BvConstExpr.construct(other, self.size), self)

    def __div__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUDivExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return (self.value / long(other)) & self.size_mask
            else:
                
                if not self.__has_value__:
                    other_value=long(other)
                    
                    #p / 0 = ERROR
                    if other_value == 0:
                        raise ZeroDivisionError

                    #p / 1 = p
                    if other_value == 1:
                        return self
                
                    #p / (2 ** x) = p >> x
                    l = math.log(other_value, 2)
                    if l > 0 and l == long(l):
                        return self >> long(l)
                else:
                    #0 / p = 0
                    if self.value == 0:
                        return 0
                    
                    #1 / p = 1 (mod n)
                    if self.value == 1:
                        return 1

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvUDivExpr.construct(self, other)

    def __rdiv__(self, other):
        if self.__has_value__:
            return (other / self.value) & self.size_mask
        else:
            #0 / p = 0
            if other == 0:
                return 0

            #1 / p = 1 (mod n)
            if other == 1:
                return 1

            return BvUDivExpr.construct(BvConstExpr.construct(other, self.size), self)

    def __mul__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvMulExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value * secondary) & self.size_mask
            else:
                #a * 0 = 0
                if value == 0:
                    return 0

                #a * 1 = a
                if value == 1:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask

                #a * -1 = -a
                if value == self.size_mask:
                    return -secondary if isinstance(secondary, BvExpr) else (-secondary) & self.size_mask
                
                #a * (2 ** x) = a << x
                l = math.log(value, 2)
                if l > 0 and l == long(l):
                    return secondary << long(l)
                
                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvMulExpr.construct(self, other)

    def __rmul__(self, other):
        return self.__mul__(other)

    def __mod__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvURemExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return (self.value % long(other)) & self.size_mask
            else:
                if not self.__has_value__:
                    other_value = long(other)
                    
                    #p mod 0 = ERROR
                    if other_value == 0:
                        raise ZeroDivisionError
                    
                    #p mod 1 = 0
                    if other_value == 1:
                        return 0

                    #p mod (2 ** x) = concat(const-0[x], extract(p, x -1, 0))
                    l = math.log(other_value, 2)
                    if l > 0 and l == long(l):
                        return BvConstExpr.construct(0, long(l)).concat(self.extract(long(l) - 1, 0))
                else:
                    #0 mod p = 0
                    if self.value == 0:
                        return 0

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvURemExpr.construct(self, other)

    def __rmod__(self, other):
        if self.__has_value__:
            return (other % self.value) & self.size_mask
        else:
            #0 mod p = 0
            if other == 0:
                return 0

            return BvURemExpr.construct(BvConstExpr.construct(other, self.size), self)

    def __eq__(self, other):
        other_is_expr = isinstance(other, BvExpr)
        if self.__has_value__ and (not other_is_expr or other.__has_value__):
            return self.value == long(other)
        else:
            if not other_is_expr:
                other = BvConstExpr.construct(other, self.size)
            
            return EqExpr.construct(self, other)

    def __ne__(self, other):
        other_is_expr = isinstance(other, BvExpr)
        if self.__has_value__ and (not other_is_expr or other.__has_value__):
            return self.value != long(other)
        else:
            if not other_is_expr:
                other = BvConstExpr.construct(other, self.size)
            
            return DistinctExpr.construct(self, other)

    def __gt__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUgtExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value > (long(other) & self.size_mask)
            else:
                #0 > p <=> False
                if self.__has_value__ and self.value == 0:
                    return False

                #p > all-1 <=> False
                if not self.__has_value__ and long(other) == self.size_mask:
                    return False

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvUgtExpr.construct(self, other)

    def __ge__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUgeExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value >= (long(other) & self.size_mask)
            else:
                #all-1 >= p <=> True
                if self.__has_value__ and self.value == self.size_mask:
                    return True

                #p >= 0 <=> True
                if not self.__has_value__ and long(other) == 0:
                    return True

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvUgeExpr.construct(self, other)

    def __lt__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUltExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value < (long(other) & self.size_mask)
            else:
                #all-1 < p <=> False
                if self.__has_value__ and self.value == self.size_mask:
                    return False

                #p < 0 <=> False
                if not self.__has_value__ and self.value == 0:
                    return False

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvUltExpr.construct(self, other)

    def __le__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUleExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value <= (long(other) & self.size_mask)
            else:
                #0 <= p <=> True
                if self.__has_value__ and self.value == 0:
                    return True

                #p <= all-1 <=> True
                if not self.__has_value__ and long(other) == self.size_mask:
                    return True

                if not other_is_expr:
                    other=BvConstExpr.construct(other, self.size)
                    
                return BvUleExpr.construct(self, other)
    

    #end and start are inclusive
    def extract(self, end, start):
        extract_size = end - start + 1
        assert extract_size + start <= self.size
        assert extract_size > 0

        if extract_size == self.size:
            return long(self) if self.__has_value__ else self

        if self.__has_value__:
            return (self.value >> start) & ((2 ** extract_size) - 1)
        
        #traverse the children tree looking for a subtree of concat expressions that covers the extract_size
        #taking into consideration the start offset
        if isinstance(self, BvConcatExpr):
            c0=self.children[0]
            c1=self.children[1]
            if extract_size + start <= c1.size:
                #included on the second child
                return c1.extract(end, start)
            elif start >= c1.size:
                #included on the first child
                return self.children[0].extract(end - c1.size, start - c1.size)
            
            #concat have the associative property:
            #concat(concat(a, b), c) == concat(a, concat(b, c))
            #IMPORTANT: the concat op must force association to the left as in this example.
            #           check the code on concat()
            if start < c1.size and isinstance(c0, BvConcatExpr):
                #concat "b" with "c"
                newchild = c0.children[1].concat(c1, force_expr=True)
                
                #concat a with (b, c)
                return BvConcatExpr.construct(c0.children[0], newchild, force_assoc=False).extract(end, start)

        #common case        
        return BvExtractExpr.construct(self, end, start)
    
    def concat(self, other, force_expr=False):
        assert isinstance(other, BvExpr) #otherwise the result is unpredictable

        if self.__has_value__ and other.__has_value__:
            val = self.value << other.size | other.value
            return BvConstExpr.construct(val, self.size + other.size) if force_expr else val
        
        if isinstance(self, BvExtractExpr) and isinstance(other, BvExtractExpr) and \
           self.children[0].__hash__() == other.children[0].__hash__():
            
            #concat(extract(x, a, j), extract(x, j-1, b)) = extract(x, a, b)
            if other.end == self.start - 1:
                return self.children[0].extract(self.end, other.start)
        
        return BvConcatExpr.construct(self, other)

    def zeroExtend(self, new_size):
        assert self.size <= new_size
        if self.size == new_size:
            return self
        
        return BvConstExpr.construct(0, new_size - self.size).concat(self)
    
    def signExtend(self, new_size):
        assert self.size <= new_size
        if self.size == new_size:
            return self

        #http://graphics.stanford.edu/~seander/bithacks.html        
        m = 1 << (self.size - 1)
        x = BvConstExpr.construct(0, new_size - self.size).concat(self)
        ret = (x ^ m) - m 
        return ret if isinstance(ret, BvExpr) else ret & ((2 ** new_size) - 1)   

class BvConstExpr(BvExpr):
    children=()
    __has_value__=True
    __depth__=1
    def __init__(self, value, size):
        #size is in bits

        self.size_mask = ((2 ** size) - 1)
        self.value=value & self.size_mask
        self.size=size
        self.__sort__="BitVec %d" % size
    
    def __str__(self):
        return ("0x%0" + str(((self.size - 1) // 4) + 1) + "x[%d]") % (self.value, self.size)
    
    def __int__(self):
        return self.value
    
    def __long__(self):
        return self.value

    @staticmethod
    def construct(name, size):
        return BvConstExpr(name, size)

class BvVarExpr(BvExpr):
    children=()
    value=None
    __depth__=1
    def __init__(self, size, name=None):
        if name == None:
            self.name = "bv_%x" % id(self)
        else:
            self.name=name
        self.size=size
        self.size_mask = ((2 ** size) - 1)
        self.__sort__="BitVec %d" % size
    
    def __str__(self):
        return "%s[%d]" % (self.name, self.size)

    @staticmethod
    def construct(size, name=None):
        return BvVarExpr(size, name)

class BvConcatExpr(BvExpr):
    __function__="concat"
    __python_op__=staticmethod(BvExpr.concat)
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size + p2.size
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__="BitVec %d" % self.size

    @staticmethod
    def construct(p1, p2, force_assoc=True, force_expr=False):
        #Force associativity to the left
        if force_assoc and isinstance(p2, BvConcatExpr):
            p1 = p1.concat(p2.children[0], force_expr=True)
            p2 = p2.children[1]
        return BvConcatExpr(p1, p2)

class BvExtractExpr(BvExpr):
    __function__="extract"
    __python_op__=staticmethod(BvExpr.extract)
    def __init__(self, p1, i, j):
        assert p1.size > i >= j >= 0

        self.__depth__=p1.__depth__ + 1
        self.children=(p1, )
        
        #start and end both include the boundaries
        self.start = j
        self.end = i
        self.size=i - j + 1
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__="BitVec %d" % self.size

    def __str__(self):
        return "%s(%s, %d, %d)" % (self.__function__, str(self.children[0]), self.end, self.start)

    @staticmethod
    def construct(p1, i, j):
        return BvExtractExpr(p1, i, j)

class BvNotExpr(BvExpr):
    __function__="bvnot"
    __python_op__=staticmethod(BvExpr.__invert__)
    def __init__(self, p1):
        self.__depth__=p1.__depth__ + 1
        self.children=(p1, )
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @staticmethod
    def construct(p1, force_expr=False):
        #!!p = p
        if isinstance(p1, BvNotExpr):
            return p1.children[0]
        return BvNotExpr(p1)

class BvNegExpr(BvExpr):
    __function__="bvneg"
    __python_op__=staticmethod(BvExpr.__neg__)
    def __init__(self, p1):
        self.__depth__=p1.__depth__ + 1
        self.children=(p1, )
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

    @staticmethod
    def construct(p1, force_expr=False):
        #-(-p) = p
        if isinstance(p1, BvNegExpr):
            return p1.children[0]
        return BvNegExpr(p1)

class BvAndExpr(BvExpr):
    __function__="bvand"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__and__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @classmethod
    def construct(cls, p1, p2, force_assoc=True, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2, force_assoc)
        p2 = BvConstExpr.construct(p2, p1.size) if not isinstance(p2, BvExpr) else p2

        #p & p = p
        if p1.__hash__() == p2.__hash__():
            return p1
        
        #p & !p = 0
        if (isinstance(p1, BvNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return 0 if not force_expr else BvConstExpr.construct(0, p1.size)
        return cls(p1, p2)

class BvOrExpr(BvExpr):
    __function__="bvor"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__or__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @classmethod
    def construct(cls, p1, p2, force_assoc=True, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2, force_assoc)
        p2 = BvConstExpr.construct(p2, p1.size) if not isinstance(p2, BvExpr) else p2        
        
        #p | p = p
        if p1.__hash__() == p2.__hash__():
            return p1
        
        #p | !p = all-1 
        if (isinstance(p1, BvNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return p1.size_mask if not force_expr else BvConstExpr.construct(p1.size_mask, p1.size)
        return cls(p1, p2)

class BvXorExpr(BvExpr):
    __function__="bvxor"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__xor__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @classmethod
    def construct(cls, p1, p2, force_assoc=True, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2, force_assoc)
        p2 = BvConstExpr.construct(p2, p1.size) if not isinstance(p2, BvExpr) else p2        

        #p ^ p = 0
        if p1.__hash__() == p2.__hash__():
            return 0 if not force_expr else BvConstExpr.construct(0, p1.size)
        
        #p ^ !p = all-1 
        if (isinstance(p1, BvNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return p1.size_mask if not force_expr else BvConstExpr.construct(p1.size_mask, p1.size)
        return cls(p1, p2)

class BvAddExpr(BvExpr):
    __function__="bvadd"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__add__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @classmethod
    def construct(cls, p1, p2, force_assoc=True, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2, force_assoc)
        p2 = BvConstExpr.construct(p2, p1.size) if not isinstance(p2, BvExpr) else p2        

        if p1.__hash__() == p2.__hash__():
            #p + p = p * 2 = p << 1
            return p1 << 1
        
        #p + (-p) == 0
        if (isinstance(p1, BvNegExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNegExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return 0 if not force_expr else BvConstExpr.construct(0, p1.size)
        return cls(p1, p2)

class BvSubExpr(BvExpr):
    __function__="bvsub"
    __python_op__=staticmethod(BvExpr.__sub__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p - p = 0
        if p1.__hash__() == p2.__hash__():
            return 0 if not force_expr else BvConstExpr.construct(0, p1.size)
        
        #p - (-p) = p + p = p * 2
        #(-p) - p = (-p) * 2
        if (isinstance(p1, BvNegExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNegExpr) and p2.children[0].__hash__() == p1.__hash__()):
            tmp=p1 * 2
            return tmp if isinstance(tmp, BvExpr) or not force_expr else BvConstExpr.construct(tmp, p1.size)
        return BvSubExpr(p1, p2)

class BvMulExpr(BvExpr):
    __function__="bvmul"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__mul__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @classmethod
    def construct(cls, p1, p2, force_assoc=True, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2, force_assoc)
        p2 = BvConstExpr.construct(p2, p1.size) if not isinstance(p2, BvExpr) else p2        
        return cls(p1, p2)

class BvUDivExpr(BvExpr):
    __function__="bvudiv"
    __python_op__=staticmethod(BvExpr.__div__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @staticmethod
    def construct(p1, p2, force_expr):
        #p / p = 1
        if p1.__hash__() == p2.__hash__():
            return 1 if not force_expr else BvConstExpr.construct(1, p1.size)
        
        #p / (-p) = -1
        if (isinstance(p1, BvNegExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNegExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return p1.size_mask if not force_expr else BvConstExpr.construct(p1.size_mask, p1.size)
        return BvUDivExpr(p1, p2)

class BvURemExpr(BvExpr):
    __function__="bvurem"
    __python_op__=staticmethod(BvExpr.__mod__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p mod p = 0
        if p1.__hash__() == p2.__hash__():
            return 0 if not force_expr else BvConstExpr.construct(0, p1.size)
        return BvURemExpr(p1, p2)

class BvShlExpr(BvExpr):
    __function__="bvshl"
    __python_op__=staticmethod(BvExpr.__lshift__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

    @staticmethod
    def construct(p1, p2):
        return BvShlExpr(p1, p2)

class BvShrExpr(BvExpr):
    __function__="bvshr"
    __python_op__=staticmethod(BvExpr.__rshift__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

    @staticmethod
    def construct(p1, p2):
        return BvShrExpr(p1, p2)
    
# Comparison (return Bool from 2 BitVec)

class BvUltExpr(BoolExpr):
    __function__="bvult"
    __python_op__=staticmethod(BvExpr.__lt__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p < p <=> False
        if p1.__hash__() == p2.__hash__():
            return False if not force_expr else FalseExpr
        return BvUltExpr(p1, p2)

class BvUleExpr(BoolExpr):
    __function__="bvule"
    __python_op__=staticmethod(BvExpr.__le__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p <= p <=> True
        if p1.__hash__() == p2.__hash__():
            return True if not force_expr else TrueExpr
        return BvUleExpr(p1, p2)

class BvUgtExpr(BoolExpr):
    __function__="bvugt"
    __python_op__=staticmethod(BvExpr.__gt__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p > p <=> False
        if p1.__hash__() == p2.__hash__():
            return False if not force_expr else FalseExpr
        return BvUgtExpr(p1, p2)

class BvUgeExpr(BoolExpr):
    __function__="bvuge"
    __python_op__=staticmethod(BvExpr.__ge__)
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p >= p <=> True
        if p1.__hash__() == p2.__hash__():
            return True if not force_expr else TrueExpr
        return BvUgeExpr(p1, p2)

class BvIteExpr(BvExpr):
    __function__="ite"
    def __init__(self, _if, _then, _else):
        assert isinstance(_if, BoolExpr)
        assert _then.__sort__ == _else.__sort__
        self.size=_then.size
        self.size_mask=_then.size_mask
        self.__sort__=_then.__sort__
        self.children=(_if, _then, _else)
        self.__depth__=max(_if.__depth__, _then.__depth__, _else.__depth__) + 1

    @staticmethod
    def construct(_if, _then, _else):
        return BvIteExpr(_if, _then, _else)

def _next_power_of_two(v):
    #up to for 32bits
    v-=1
    v |= v >> 1
    v |= v >> 2
    v |= v >> 4
    v |= v >> 8
    v |= v >> 16
    v+=1
    return v

LRUCACHE_SIZE=1000

#Remeber to initialize the LRU cache with the "most cache-able" expression for extra speed
BvConstExpr.construct = staticmethod(LruCache(BvConstExpr.construct, maxsize = LRUCACHE_SIZE)) 
_BvExprCache = BvConstExpr.construct.shared_parameters

for cls in (BvVarExpr, BvConcatExpr, BvExtractExpr, BvNotExpr, BvNegExpr, \
            BvAndExpr, BvOrExpr, BvXorExpr, BvAddExpr, BvSubExpr, BvMulExpr, \
            BvUDivExpr, BvURemExpr, BvShlExpr, BvShrExpr, \
            BvUgtExpr, BvUgeExpr, BvUltExpr, BvUleExpr, \
            BvIteExpr):
    cls.construct = staticmethod(LruCache(cls.construct, shared_parameters=_BvExprCache)) 
