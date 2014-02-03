from emulator.symbolic.base_expr import Expr
from emulator.symbolic.boolean_expr import EqExpr, DistinctExpr, BoolExpr, TrueExpr, FalseExpr
from utils.lru import LruCache
import math

#helpers
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

def toExpr(val, size):
    return val if isinstance(val, BvExpr) else val & ((2 ** size) - 1)

def forceToExpr(val, size):
    return val if isinstance(val, BvExpr) else BvConstExpr.construct(val, size)

def forceToExprCond(cond, val, size):
    return forceToExpr(val) if cond else val

class BvExpr(Expr):
    __slots__=("size", "size_mask", "__sort__")
    __base_sort__="BitVec"
    
    @classmethod
    def __associative_construct__(cls, p1, p2):
        #float constants to the right
        if isinstance(p1, BvConstExpr):
            tmp = p2
            p2 = p1
            p1 = tmp
    
        #Force associativity to the right
        #(a * b) * c   <=>   a * (b * c)
        #   p1     p2
        if isinstance(p1, cls):
            p2 = cls.__python_op__(p1.children[1], p2) #b * c
            p1 = p1.children[0] #a
        
        return p1, p2
    
    def __nonzero__(self):
        raise Exception, "A BitVector Expression cannot be evaluated to boolean"
    
    def __len__(self):
        return self.size
    
    def __pos__(self):
        return self

    def __and__(self, other):
        if isinstance(other, BvExpr) and not other.__has_value__ and not self.__has_value__:
            return BvAndExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return value & secondary
            else:
                #secondary is a BvExpr

                #p & 0 = 0
                if value == 0:
                    return 0
                
                #p & all-1 = p
                if value == self.size_mask:
                    return secondary
                
                #p & ((2 ** l) - 1) = p mod (2 ** l) 
                l = math.log(value + 1, 2)
                if l > 0 and l == long(l):
                    return BvConstExpr.construct(0, self.size - long(l)).concat(self.extract(long(l) - 1, 0))

                return BvAndExpr.construct(self, forceToExpr(other, self.size))

    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        if isinstance(other, BvExpr) and not other.__has_value__ and not self.__has_value__:
            return BvOrExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return toExpr(value | secondary, self.size)
            else:
                #p | 0 = p
                if value == 0:
                    return secondary
                
                #p | all-1 = all-1
                if value == self.size_mask:
                    return self.size_mask

                #p | ((2 ** l) - 1) = concat(p_high, all-1-l-size) 
                l = math.log(value + 1, 2)
                if l > 0 and l == long(l):
                    return self.extract(self.size - 1, long(l)).concat(BvConstExpr.construct(value, long(l)))

                return BvOrExpr.construct(self, forceToExpr(other, self.size))

    def __ror__(self, other):
        return self.__or__(other)
    
    def __xor__(self, other):
        if isinstance(other, BvExpr) and not other.__has_value__ and not self.__has_value__:
            return BvXorExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return toExpr(value ^ secondary, self.size)
            else:
                #secondary is a BvExpr

                #p ^ 0 = p
                if value == 0:
                    return secondary
                
                #p ^ all-1 = ~p
                if value == self.size_mask:
                    return ~secondary

                return BvXorExpr.construct(self, forceToExpr(other, self.size))

    def __rxor__(self, other):
        return self.__xor__(other)
    
    def __invert__(self):
        if self.__has_value__:
            return toExpr(~self.value, self.size)
        else:
            return BvNotExpr.construct(self)
    
    def __neg__(self):
        if self.__has_value__:
            return toExpr(-self.value, self.size)
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

                # 0 >> p = 0
                elif self.value == 0:
                    return 0

                return BvShrExpr.construct(self, forceToExpr(other, self.size))

    def __rrshift__(self, other):
        if self.__has_value__:
            return toExpr(other >> self.value, self.size)
        else:
            # 0 >> p = 0
            if other == 0:
                return 0
            return BvShrExpr.construct(forceToExpr(other, self.size), self)
    
    def __lshift__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvShlExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or other.__has_value__):
                return toExpr(self.value << long(other), self.size)
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
                
                # 0 << p = 0
                elif self.value == 0:
                    return 0

                return BvShlExpr.construct(self, forceToExpr(other, self.size))

    def __rlshift__(self, other):
        if self.__has_value__:
            return toExpr(other << self.value, self.size)
        else:
            # 0 << p = 0
            if other == 0:
                return 0
            return BvShlExpr.construct(forceToExpr(other, self.size), self)

    def __add__(self, other):
        if isinstance(other, BvExpr) and not other.__has_value__ and not self.__has_value__:
            return BvAddExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return toExpr(value + secondary, self.size)
            else:
                #secondary is a BvExpr

                #p + 0 = p
                if value == 0:
                    return secondary
                
                return BvAddExpr.construct(self, forceToExpr(other, self.size))

    def __radd__(self, other):
        return self.__add__(other)

    def __sub__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvSubExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or other.__has_value__):
                return toExpr(self.value - long(other), self.size)
            else:
                #p - 0 = p
                if not self.__has_value__ and long(other) == 0:
                    return self
                
                #0 - p = -p
                if self.__has_value__ and self.value == 0:
                    return toExpr(-other, self.size)

                return BvSubExpr.construct(self, forceToExpr(other, self.size))

    def __rsub__(self, other):
        if self.__has_value__:
            return toExpr(other - self.value, self.size)
        else:
            #0 - p = -p
            if other == 0:
                return -self

            return BvSubExpr.construct(forceToExpr(other, self.size), self)

    def __div__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUDivExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return toExpr(self.value / long(other), self.size)
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

                return BvUDivExpr.construct(self, forceToExpr(other, self.size))

    def __rdiv__(self, other):
        if self.__has_value__:
            return toExpr(other / self.value, self.size)
        else:
            #0 / p = 0
            if other == 0:
                return 0

            #1 / p = 1 (mod n)
            if other == 1:
                return 1

            return BvUDivExpr.construct(forceToExpr(other, self.size), self)

    def __mul__(self, other):
        if isinstance(other, BvExpr) and not other.__has_value__ and not self.__has_value__:
            return BvMulExpr.construct(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return toExpr(value * secondary, self.size)
            else:
                #secondary is a BvExpr

                #a * 0 = 0
                if value == 0:
                    return 0

                #a * 1 = a
                if value == 1:
                    return secondary

                #a * -1 = -a
                if value == self.size_mask:
                    return -secondary
                
                return BvMulExpr.construct(self, forceToExpr(other, self.size))

    def __rmul__(self, other):
        return self.__mul__(other)

    def __mod__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvURemExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return toExpr(self.value % long(other), self.size)
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
                        return BvConstExpr.construct(0, self.size - long(l)).concat(self.extract(long(l) - 1, 0))
                else:
                    #0 mod p = 0
                    if self.value == 0:
                        return 0

                return BvURemExpr.construct(self, forceToExpr(other, self.size))

    def __rmod__(self, other):
        if self.__has_value__:
            return other % self.value
        else:
            #0 mod p = 0
            if other == 0:
                return 0

            return BvURemExpr.construct(forceToExpr(other, self.size), self)

    def __eq__(self, other):
        if self.__has_value__ and (not isinstance(other, BvExpr) or other.__has_value__):
            return self.value == long(other)
        else:
            return EqExpr.construct(self, forceToExpr(other, self.size))

    def __ne__(self, other):
        if self.__has_value__ and (not isinstance(other, BvExpr) or other.__has_value__):
            return self.value != long(other)
        else:
            return DistinctExpr.construct(self, forceToExpr(other, self.size))

    def __gt__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUgtExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value > toExpr(long(other), self.size)
            else:
                #0 > p <=> False
                if self.__has_value__ and self.value == 0:
                    return False

                #p > all-1 <=> False
                if not self.__has_value__ and long(other) == self.size_mask:
                    return False

                return BvUgtExpr.construct(self, forceToExpr(other, self.size))

    def __ge__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUgeExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value >= toExpr(long(other), self.size)
            else:
                #all-1 >= p <=> True
                if self.__has_value__ and self.value == self.size_mask:
                    return True

                #p >= 0 <=> True
                if not self.__has_value__ and long(other) == 0:
                    return True

                return BvUgeExpr.construct(self, forceToExpr(other, self.size))

    def __lt__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUltExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value < toExpr(long(other), self.size)
            else:
                #all-1 < p <=> False
                if self.__has_value__ and self.value == self.size_mask:
                    return False

                #p < 0 <=> False
                if not self.__has_value__ and self.value == 0:
                    return False

                return BvUltExpr.construct(self, forceToExpr(other, self.size))

    def __le__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvUleExpr.construct(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value <= toExpr(long(other), self.size)
            else:
                #0 <= p <=> True
                if self.__has_value__ and self.value == 0:
                    return True

                #p <= all-1 <=> True
                if not self.__has_value__ and long(other) == self.size_mask:
                    return True

                return BvUleExpr.construct(self, forceToExpr(other, self.size))
    

    #end and start are inclusive
    def extract(self, end, start):
        extract_size = end - start + 1
        assert extract_size + start <= self.size
        assert extract_size > 0

        if extract_size == self.size:
            return long(self) if self.__has_value__ else self

        if self.__has_value__:
            return toExpr(self.value >> start, extract_size)
        
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
            if force_expr:
                return forceToExpr(val, self.size + other.size)
            else:
                return toExpr(val, self.size + other.size)
        
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
        return toExpr(ret, new_size)   

class BvConstExpr(BvExpr):
    __slots__=("value")
    children=()
    __has_value__=True
    __depth__=1
    __backend_fun__=lambda: None
    def __init__(self, value, size):
        #size is in bits

        self.size_mask = ((2 ** size) - 1)
        self.value=value & self.size_mask
        self.size=size
        self.__sort__="(_ BitVec %d)" % size
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    def __str__(self):
        return ("0x%0" + str(((self.size - 1) // 4) + 1) + "x[%d]") % (self.value, self.size)
    
    def __export__(self):
        if self.size % 4 == 0:
            return ("#x%0" + str(((self.size - 1) // 4) + 1) + "x") % self.value
        else:
            return ("#b{0:0" + str(self.size) + "b}").format(self.value)

    def __int__(self):
        return self.value
    
    def __long__(self):
        return self.value

    @staticmethod
    def construct(value, size):
        return BvConstExpr(value, size)

class BvVarExpr(BvExpr):
    __slots__=("name")
    children=()
    value=None
    __depth__=1
    __backend_fun__=lambda: None
    def __init__(self, size, name=None):
        if name == None:
            self.name = "bv_%x" % id(self)
        else:
            self.name=name
        self.size=size
        self.size_mask = ((2 ** size) - 1)
        self.__sort__="(_ BitVec %d)" % size
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    def __str__(self):
        return "%s[%d]" % (self.name, self.size)

    def __export__(self):
        return self.name

    @staticmethod
    def construct(size, name=None):
        return BvVarExpr(size, name)

class BvConcatExpr(BvExpr):
    __slots__=()
    __function__="concat"
    __python_op__=staticmethod(BvExpr.concat)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size + p2.size
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__="(_ BitVec %d)" % self.size
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2, force_assoc=True):
        #Force associativity to the left
        if force_assoc and isinstance(p2, BvConcatExpr):
            p1 = p1.concat(p2.children[0])
            p2 = p2.children[1]
        return BvConcatExpr(p1, p2)

class BvExtractExpr(BvExpr):
    __slots__=("start", "end")
    __function__="extract"
    __python_op__=staticmethod(BvExpr.extract)
    __backend_fun__=lambda: None
    def __init__(self, p1, i, j):
        assert p1.size > i >= j >= 0

        self.__depth__=p1.__depth__ + 1
        self.children=(p1, )
        
        #start and end both include the boundaries
        self.start = j
        self.end = i
        self.size=i - j + 1
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__="(_ BitVec %d)" % self.size
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    def __str__(self):
        return "%s(%s, %d, %d)" % (self.__function__, str(self.children[0]), self.end, self.start)
    
    def __export__(self):
        return "((_ extract %d %d) %s)" % (self.end, self.start, self.children[0].export())

    @staticmethod
    def construct(p1, i, j):
        return BvExtractExpr(p1, i, j)

class BvNotExpr(BvExpr):
    __slots__=()
    __function__="bvnot"
    __python_op__=staticmethod(BvExpr.__invert__)
    __backend_fun__=lambda: None
    def __init__(self, p1):
        self.__depth__=p1.__depth__ + 1
        self.children=(p1, )
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @staticmethod
    def construct(p1):
        #!!p = p
        if isinstance(p1, BvNotExpr):
            return p1.children[0]
        return BvNotExpr(p1)

class BvNegExpr(BvExpr):
    __slots__=()
    __function__="bvneg"
    __python_op__=staticmethod(BvExpr.__neg__)
    __backend_fun__=lambda: None
    def __init__(self, p1):
        self.__depth__=p1.__depth__ + 1
        self.children=(p1, )
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1):
        #-(-p) = p
        if isinstance(p1, BvNegExpr):
            return p1.children[0]
        return BvNegExpr(p1)

class BvAndExpr(BvExpr):
    __slots__=()
    __function__="bvand"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__and__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @classmethod
    def construct(cls, p1, p2, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2)
        p2 = forceToExpr(p2, p1.size)

        #p & p = p
        if p1.__hash__() == p2.__hash__():
            return p1
        
        #p & !p = 0
        if (isinstance(p1, BvNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return forceToExprCond(force_expr, 0, p1.size)
        return cls(p1, p2)

class BvOrExpr(BvExpr):
    __slots__=()
    __function__="bvor"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__or__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @classmethod
    def construct(cls, p1, p2, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2)
        p2 = forceToExpr(p2, p1.size)        
        
        #p | p = p
        if p1.__hash__() == p2.__hash__():
            return p1
        
        #p | !p = all-1 
        if (isinstance(p1, BvNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return forceToExprCond(force_expr, p1.size_mask, p1.size)
        return cls(p1, p2)

class BvXorExpr(BvExpr):
    __slots__=()
    __function__="bvxor"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__xor__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @classmethod
    def construct(cls, p1, p2, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2)
        p2 = forceToExpr(p2, p1.size)        

        #p ^ p = 0
        if p1.__hash__() == p2.__hash__():
            return forceToExprCond(force_expr, 0, p1.size)
        
        #p ^ !p = all-1 
        if (isinstance(p1, BvNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return forceToExprCond(force_expr, p1.size_mask, p1.size)
        return cls(p1, p2)

class BvAddExpr(BvExpr):
    __slots__=()
    __function__="bvadd"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__add__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @classmethod
    def construct(cls, p1, p2, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2)
        p2 = forceToExpr(p2, p1.size)        

        #p + p = p * 2
        if p1.__hash__() == p2.__hash__():
            return forceToExprCond(force_expr, p1 * 2, p1.size)
        
        #p + (p + q) = (p * 2) + q  (warantied by the __associative_construct__ function)
        if isinstance(p2, BvAddExpr):
            if   p1.__hash__() == p2.children[0].__hash__():
                return forceToExprCond(force_expr, (p1 * 2) + p2.children[1], p1.size)
            elif p1.__hash__() == p2.children[1].__hash__():
                return forceToExprCond(force_expr, (p1 * 2) + p2.children[0], p1.size)
        
        #(p * q) + p = p * (q+1)
        if isinstance(p1, BvMulExpr):
            if   p1.children[0].__hash__() == p2.__hash__():
                return forceToExprCond(force_expr, p2 * (p1.children[1] + 1), p1.size) 
            elif p1.children[1].__hash__() == p2.__hash__():
                return forceToExprCond(force_expr, p2 * (p1.children[0] + 1), p1.size) 
        
        #p + (p * q) = p * (q+1)
        if isinstance(p2, BvMulExpr): 
            if   p2.children[0].__hash__() == p1.__hash__():
                return forceToExprCond(force_expr, p1 * (p2.children[1] + 1), p2.size) 
            elif p2.children[1].__hash__() == p1.__hash__():
                return forceToExprCond(force_expr, p1 * (p2.children[0] + 1), p2.size) 
        
        #p + (-p) == 0
        if (isinstance(p1, BvNegExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNegExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return forceToExprCond(force_expr, 0, p1.size)
        return cls(p1, p2)

class BvSubExpr(BvExpr):
    __slots__=()
    __function__="bvsub"
    __python_op__=staticmethod(BvExpr.__sub__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p - p = 0
        if p1.__hash__() == p2.__hash__():
            return forceToExprCond(force_expr, 0, p1.size)
        
        #p - (-p) = p + p = p * 2
        #(-p) - p = (-p) * 2
        if (isinstance(p1, BvNegExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNegExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return forceToExprCond(force_expr, p1 * 2, p1.size)
        
        #(p * q) - p = p * (q-1)
        if isinstance(p1, BvMulExpr):
            if   p1.children[0].__hash__() == p2.__hash__():
                return forceToExprCond(force_expr, p2 * (p1.children[1] - 1), p1.size) 
            elif p1.children[1].__hash__() == p2.__hash__():
                return forceToExprCond(force_expr, p2 * (p1.children[0] - 1), p1.size) 
        return BvSubExpr(p1, p2)

class BvMulExpr(BvExpr):
    __slots__=()
    __function__="bvmul"
    __commutative__=True
    __python_op__=staticmethod(BvExpr.__mul__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size

        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @classmethod
    def construct(cls, p1, p2, force_expr=False):
        p1, p2 = cls.__associative_construct__(p1, p2)
        p2 = forceToExpr(p2, p1.size)        
        return cls(p1, p2)

class BvUDivExpr(BvExpr):
    __slots__=()
    __function__="bvudiv"
    __python_op__=staticmethod(BvExpr.__div__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @staticmethod
    def construct(p1, p2, force_expr):
        #p / p = 1
        if p1.__hash__() == p2.__hash__():
            return forceToExprCond(force_expr, 1, p1.size)
        
        #p / (-p) = -1
        if (isinstance(p1, BvNegExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BvNegExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return forceToExprCond(force_expr, p1.size_mask, p1.size)
        return BvUDivExpr(p1, p2)

class BvURemExpr(BvExpr):
    __slots__=()
    __function__="bvurem"
    __python_op__=staticmethod(BvExpr.__mod__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p mod p = 0
        if p1.__hash__() == p2.__hash__():
            return forceToExprCond(force_expr, 0, p1.size)
        return BvURemExpr(p1, p2)

class BvShlExpr(BvExpr):
    __slots__=()
    __function__="bvshl"
    __python_op__=staticmethod(BvExpr.__lshift__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2):
        return BvShlExpr(p1, p2)

class BvShrExpr(BvExpr):
    __slots__=()
    __function__="bvshr"
    __python_op__=staticmethod(BvExpr.__rshift__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2):
        return BvShrExpr(p1, p2)
    
# Comparison (return Bool from 2 BitVec)

class BvUltExpr(BoolExpr):
    __slots__=()
    __function__="bvult"
    __python_op__=staticmethod(BvExpr.__lt__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p < p <=> False
        if p1.__hash__() == p2.__hash__():
            return False if not force_expr else FalseExpr
        return BvUltExpr(p1, p2)

class BvUleExpr(BoolExpr):
    __slots__=()
    __function__="bvule"
    __python_op__=staticmethod(BvExpr.__le__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p <= p <=> True
        if p1.__hash__() == p2.__hash__():
            return True if not force_expr else TrueExpr
        return BvUleExpr(p1, p2)

class BvUgtExpr(BoolExpr):
    __slots__=()
    __function__="bvugt"
    __python_op__=staticmethod(BvExpr.__gt__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p > p <=> False
        if p1.__hash__() == p2.__hash__():
            return False if not force_expr else FalseExpr
        return BvUgtExpr(p1, p2)

class BvUgeExpr(BoolExpr):
    __slots__=()
    __function__="bvuge"
    __python_op__=staticmethod(BvExpr.__ge__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p >= p <=> True
        if p1.__hash__() == p2.__hash__():
            return True if not force_expr else TrueExpr
        return BvUgeExpr(p1, p2)

class BvIteExpr(BvExpr):
    __slots__=()
    __function__="ite"
    __backend_fun__=lambda: None
    def __init__(self, _if, _then, _else):
        assert isinstance(_if, BoolExpr)
        assert _then.__sort__ == _else.__sort__
        self.size=_then.size
        self.size_mask=_then.size_mask
        self.__sort__=_then.__sort__
        self.children=(_if, _then, _else)
        self.__depth__=max(_if.__depth__, _then.__depth__, _else.__depth__) + 1
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(_if, _then, _else):
        return BvIteExpr(_if, _then, _else)

LRUCACHE_SIZE=1000

#Remeber to initialize the LRU cache with the "most cache-able" expression for extra speed
from emulator.symbolic.memory import DeferredMemRead
DeferredMemRead.construct = staticmethod(LruCache(DeferredMemRead.construct, maxsize = LRUCACHE_SIZE)) 
BvExprCache = DeferredMemRead.construct

for cls in (BvConstExpr, BvVarExpr, BvConcatExpr, BvExtractExpr, BvNotExpr, BvNegExpr, \
            BvAndExpr, BvOrExpr, BvXorExpr, BvAddExpr, BvSubExpr, BvMulExpr, \
            BvUDivExpr, BvURemExpr, BvShlExpr, BvShrExpr, \
            BvUgtExpr, BvUgeExpr, BvUltExpr, BvUleExpr, \
            BvIteExpr):
    cls.construct = staticmethod(LruCache(cls.construct, shared_parameters=BvExprCache.shared_parameters))
 