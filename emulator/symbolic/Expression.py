'''
Created on Jul 21, 2013

@author: pablo

Boolean and Bitwise
    AND
    OR
    NOT
    XOR

Shifts
    SHL
    SHR

Arithmetic
    ADD
    SUB
    MUL
    UDIV
    UREM
    NEG

Ordering
    ULT
    ULE
    UGT
    UGE

Equality
    EQ
    NEQ

Miscellaneous
    CONCAT
    EXTRACT
    ITE
    ZEROEXTEND
    SIGNEXTEND

Constants
    FALSE
    TRUE
    BVCONST

Variables
    BOOL
    BV

Expressions
    BoolExpr
        have pythonic methods for all typical boolean operations
    BVExpr
        have pythonic method for BV operations.
        it never adapts the size of the expression by itself
    
    Once created, the expression should be considered immutable.
    __init__ functions should be avoided as much as possible.
    All type information should be static and part of the class definition.
'''

import sys

class Expr:
    __has_value__=False

    def __str__(self):
        children_repr=[str(x) for x in self.children]
        return "%s(%s)" % (self.__function__, ", ".join(children_repr))

    def export(self, fmt="smtlib2"):
        pass

    def getValue(self, val):
        """
        it's assumed that one of the two element does have a value.
        
        returns (value, secondary_value_or_expr, bool_are_both_values)
        """

        if self.__has_value__:
            val_is_expr = isinstance(val, Expr)
            if val_is_expr and val.__has_value__:
                return (self.value, val.value, True)
            else:
                return (self.value, val, not val_is_expr)
        else:
            if isinstance(val, Expr):
                return (val.value, self, False)
            else:
                return (val, self, False)

# Boolean sort and functions    
class BoolExpr(Expr):
    __sort__="Bool"
    
    def __and__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            return BoolAndExpr(self, other)
        else:
            (value, secondary, _) = self.getValue(other)
            #p & T <=> p, p & F <=> F
            return secondary if value else False

    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            return BoolOrExpr(self, other)
        else:
            (value, secondary, _) = self.getValue(other)
            #p | T <=> T, p | F <=> p
            return True if value else secondary

    def __ror__(self, other):
        return self.__or__(other)
    
    def __xor__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            return BoolXorExpr(self, other)
        else:
            (value, secondary, _) = self.getValue(other)
            #p ^ T <=> ~p, p ^ F <=> p
            return ~secondary if value else secondary 

    def __rxor__(self, other):
        return self.__xor__(other)
    
    def __invert__(self):
        if self.__has_value__:
            return not self.value
        else:
            return BoolNotExpr(self)
    
    def __ge__(self, other):
        #using => for Implication

        other_is_expr = isinstance(other, BoolExpr)
        if other_is_expr and not other.__has_value__ \
            and not self.__has_value__:
            return BoolImplExpr(self, other)
        else:
            if not other_is_expr or other.__has_value__:
                #p => T <=> T, p => F <=> ~p
                #~self is simplified on the check for __has_value__ in __invert__
                return True if bool(other) else ~self
            else:
                return BoolImplExpr(self, other)
    
    def __le__(self, other):
        #This is only for the reversed case of implication
        #other is never an expression.

        #T => p <=> p, F => p <=> T
        if self.__has_value__:
            return bool(self) if bool(other) else True
        else:
            return self if bool(other) else True
    
    def __eq__(self, other):
        other_is_expr = isinstance(other, BoolExpr)
        if self.__has_value__ and (not other_is_expr or \
            other.__has_value__):
            return bool(self) == bool(other)
        else:
            if not other_is_expr:
                other = TrueExpr if bool(other) else FalseExpr
            return EqExpr(self, other)

    def __ne__(self, other):
        other_is_expr = isinstance(other, BoolExpr)
        if self.__has_value__ and (not other_is_expr or \
            other.__has_value__):
            return bool(self) != bool(other)
        else:
            if not other_is_expr:
                other = TrueExpr if bool(other) else FalseExpr
            return DistinctExpr(self, other)


class BoolVarExpr(BoolExpr):
    children=()
    value=None
    def __init__(self, name=None):
        if name == None:
            self.name = "bool_%x" % id(self)
        else:
            self.name=name
    
    def __str__(self):
        return self.name

class _TrueExpr(BoolExpr):
    __function__="true"
    children=()
    __has_value__=True
    value=True
    def __str__(self):
        return self.__function__
    def __nonzero__(self):
        return True
TrueExpr=_TrueExpr() #singleton

class _FalseExpr(BoolExpr):
    __function__="false"
    children=()
    __has_value__=True
    value=False
    def __str__(self):
        return self.__function__
    def __nonzero__(self):
        return False
FalseExpr=_FalseExpr() #singleton

class BoolAndExpr(BoolExpr):
    __function__="and"
    def __init__(self, p1, p2):
        self.children=(p1, p2)

class BoolOrExpr(BoolExpr):
    __function__="or"
    def __init__(self, p1, p2):
        self.children=(p1, p2)

class BoolXorExpr(BoolExpr):
    __function__="xor"
    def __init__(self, p1, p2):
        self.children=(p1, p2)

class BoolNotExpr(BoolExpr):
    __function__="not"
    def __init__(self, p1):
        self.children=(p1, )

class BoolImplExpr(BoolExpr):
    __function__="=>"
    def __init__(self, p1, p2):
        self.children=(p1, p2)


# Core functions

class EqExpr(BoolExpr):
    __function__="="
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        assert p1.__sort__ == p2.__sort__

class DistinctExpr(BoolExpr):
    __function__="distinct"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        assert p1.__sort__ == p2.__sort__


# BitVector sort and functions

class BvExpr(Expr):
    __base_sort__="BitVec"
    
    def __nonzero__(self):
        raise Exception, "A BitVector Expression cannot be evaluated to boolean"
    
    def __len__(self):
        return self.size

    def __and__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvAndExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) & long(other)) & ((2 ** self.size) - 1)
            else:
                return BvAndExpr(self, BvConstExpr(other, self.size))

    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvOrExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) | long(other)) & ((2 ** self.size) - 1)
            else:
                return BvOrExpr(self, BvConstExpr(other, self.size))

    def __ror__(self, other):
        return self.__or__(other)
    
    def __xor__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvXorExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) ^ long(other)) & ((2 ** self.size) - 1)
            else:
                return BvXorExpr(self, BvConstExpr(other, self.size))

    def __rxor__(self, other):
        return self.__xor__(other)
    
    def __invert__(self):
        if self.__has_value__ == False:
            return BvNotExpr(self)
        else:
            return (~long(self)) & ((2 ** self.size) - 1)
    
    def __neg__(self):
        if self.__has_value__ == False:
            return BvNegExpr(self)
        else:
            return (-long(self)) & ((2 ** self.size) - 1)
    
    def __rshift__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvShrExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) >> long(other)) & ((2 ** self.size) - 1)
            else:
                return BvShrExpr(self, BvConstExpr(other, self.size))

    def __rrshift__(self, other):
        if self.__has_value__:
            return (long(other) >> long(self)) & ((2 ** self.size) - 1)
        else:
            return BvShrExpr(BvConstExpr(other, self.size), self)
    
    def __lshift__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvShlExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) << long(other)) & ((2 ** self.size) - 1)
            else:
                return BvShlExpr(self, BvConstExpr(other, self.size))

    def __rlshift__(self, other):
        if self.__has_value__:
            return (long(other) << long(self)) & ((2 ** self.size) - 1)
        else:
            return BvShlExpr(BvConstExpr(other, self.size), self)

    def __add__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvAddExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) + long(other)) & ((2 ** self.size) - 1)
            else:
                return BvAddExpr(self, BvConstExpr(other, self.size))

    def __radd__(self, other):
        return self.__add__(other)

    def __sub__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvSubExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) - long(other)) & ((2 ** self.size) - 1)
            else:
                return BvSubExpr(self, BvConstExpr(other, self.size))

    def __rsub__(self, other):
        if self.__has_value__:
            return (long(other) - long(self)) & ((2 ** self.size) - 1)
        else:
            return BvSubExpr(BvConstExpr(other, self.size), self)

    def __div__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvUDivExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) / long(other)) & ((2 ** self.size) - 1)
            else:
                return BvUDivExpr(self, BvConstExpr(other, self.size))

    def __rdiv__(self, other):
        if self.__has_value__:
            return (long(other) / long(self)) & ((2 ** self.size) - 1)
        else:
            return BvUDivExpr(BvConstExpr(other, self.size), self)

    def __mul__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvMulExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) * long(other)) & ((2 ** self.size) - 1)
            else:
                return BvMulExpr(self, BvConstExpr(other, self.size))

    def __rmul__(self, other):
        return self.__mul__(other)

    def __mod__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvURemExpr(self, other)
        else:
            if self.__has_value__:
                return (long(self) % long(other)) & ((2 ** self.size) - 1)
            else:
                return BvURemExpr(self, BvConstExpr(other, self.size))

    def __rmod__(self, other):
        if self.__has_value__:
            return (long(other) % long(self)) & ((2 ** self.size) - 1)
        else:
            return BvURemExpr(BvConstExpr(other, self.size), self)

    def __gt__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvUgtExpr(self, other)
        else:
            if self.__has_value__:
                return long(self) > (long(other) & ((2 ** self.size) - 1))
            else:
                return BvUgtExpr(self, BvConstExpr(other, self.size))

    def __eq__(self, other):
        if self.__has_value__ and \
           isinstance(other, BvExpr) and other.__has_value__:
            return long(self) == long(other)
        else:
            if not isinstance(other, BvExpr):
                other = BvConstExpr(other, self.size)
            return EqExpr(self, other)

    def __ne__(self, other):
        if self.__has_value__ and \
           isinstance(other, BvExpr) and other.__has_value__:
            return long(self) != long(other)
        else:
            if not isinstance(other, BvExpr):
                other = BvConstExpr(other, self.size)
            return DistinctExpr(self, other)

    def __ge__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvUgeExpr(self, other)
        else:
            if self.__has_value__:
                return long(self) >= (long(other) & ((2 ** self.size) - 1))
            else:
                return BvUgeExpr(self, BvConstExpr(other, self.size))

    def __gt__(self, other):
        if isinstance(other, BvExpr) and other.__has_value__ == False:
            return BvUgtExpr(self, other)
        else:
            if self.__has_value__:
                return long(self) > (long(other) & ((2 ** self.size) - 1))
            else:
                return BvUgtExpr(self, BvConstExpr(other, self.size))

class BvConstExpr(BvExpr):
    children=()
    __has_value__=True
    def __init__(self, value, size):
        self.value=value & ((2 ** size) - 1)
        self.size=size
        self.__sort__="BitVec %d" % size
    
    def __str__(self):
        return ("0x%0" + str(((self.size - 1) // 4) + 1) + "x[%d]") % (self.value, self.size)
    
    def __int__(self):
        return self.value
    
    def __long__(self):
        return self.value

class BvVarExpr(BvExpr):
    children=()
    value=None
    def __init__(self, size, name=None):
        if name == None:
            self.name = "bv_%x" % id(self)
        else:
            self.name=name
        self.size=size
        self.__sort__="BitVec %d" % size
    
    def __str__(self):
        return "%s[%d]" % (self.name, self.size)

class BvConcatExpr(BvExpr):
    __function__="concat"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size + p2.size
        self.__sort__="BitVec %d" % self.size

class BvExtractExpr(BvExpr):
    __function__="extract"
    def __init__(self, p1, i, j):
        self.children=(p1, )
        
        #start and end both include the boundaries
        self.start = j
        self.end = i
        self.size=i - j + 1
        self.__sort__="BitVec %d" % self.size
        assert p1.size > i >= j >= 0

class BvNotExpr(BvExpr):
    __function__="bvnot"
    def __init__(self, p1):
        self.children=(p1, )
        self.size=p1.size
        self.__sort__=p1.__sort__

class BvNegExpr(BvExpr):
    __function__="bvneg"
    def __init__(self, p1):
        self.children=(p1, )
        self.size=p1.size
        self.__sort__=p1.__sort__

class BvAndExpr(BvExpr):
    __function__="bvand"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvOrExpr(BvExpr):
    __function__="bvor"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvXorExpr(BvExpr):
    __function__="bvxor"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvAddExpr(BvExpr):
    __function__="bvadd"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvSubExpr(BvExpr):
    __function__="bvsub"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvMulExpr(BvExpr):
    __function__="bvmul"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvUDivExpr(BvExpr):
    __function__="bvudiv"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvURemExpr(BvExpr):
    __function__="bvurem"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size
    
class BvShlExpr(BvExpr):
    __function__="bvshl"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvShrExpr(BvExpr):
    __function__="bvshr"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

# Comparison (return Bool from 2 BitVec)

class BvUltExpr(BoolExpr):
    __function__="bvult"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        assert p1.size == p2.size

class BvUleExpr(BoolExpr):
    __function__="bvule"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        assert p1.size == p2.size

class BvUgtExpr(BoolExpr):
    __function__="bvugt"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        assert p1.size == p2.size

class BvUgeExpr(BoolExpr):
    __function__="bvuge"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        assert p1.size == p2.size

# Handy constructions
def BvZeroExtend(expr, new_size):
    assert isinstance(expr, BvExpr)
    assert expr.size <= new_size
    if expr.size == new_size:
        return expr
    
    return BvConcatExpr(BvConstExpr(0, new_size - expr.size), expr)

def BvSignExtend(expr, new_size):
    assert isinstance(expr, BvExpr)
    assert expr.size <= new_size
    if expr.size == new_size:
        return expr
    
    out=expr
    sign_bit=BvExtractExpr(expr, expr.size-1, expr.size-1)
    for _ in range(new_size - expr.size):
        out=BvConcatExpr(sign_bit, out)
    
    return out


# ITE is a special case because the result of the function depends of the
# parameters

class _BvIteExpr(BvExpr):
    __function__="ite"
    def __init__(self, _if, _then, _else):
        assert isinstance(_if, BoolExpr)
        assert _then.__sort__ == _else.__sort__
        self.children=(_if, _then, _else)

class _BoolIteExpr(BvExpr):
    __function__="ite"
    def __init__(self, _if, _then, _else):
        assert isinstance(_if, BoolExpr)
        assert _then.__sort__ == _else.__sort__
        self.children=(_if, _then, _else)

def IteExpr(_if, _then, _else):
    if isinstance(_if, BoolExpr) and _if.__has_value__ == False:
        if not isinstance(_then, Expr):
            if isinstance(_then, bool):
                _then=TrueExpr if _then else FalseExpr
            else:
                raise Exception, "Invalid 'then' argument on ITE"
    
        if not isinstance(_else, Expr):
            if isinstance(_else, bool):
                _else=TrueExpr if _else else FalseExpr
            else:
                raise Exception, "Invalid 'else' argument on ITE"

        if isinstance(_then, BoolExpr):
            return _BoolIteExpr(_if, _then, _else)
        else:
            return _BvIteExpr(_if, _then, _else)
    else:
        return _then if bool(_if) else _else


def test():
    t=TrueExpr
    f=BoolVarExpr()
    #print ((~t) & f) >> t, type(((~t) & f) >> t)
    x=True >> FalseExpr
    print "1)", x, type(x)
    print "2)", TrueExpr >> FalseExpr, type(TrueExpr >> FalseExpr)
    print "3)", TrueExpr >> False, type(TrueExpr >> False)

    bv1=BvConstExpr(0xcafecafe, 32)
    bv2=BvVarExpr(64, "r0")
    print BvZeroExtend(bv1, 64) ^ bv2
    
    print IteExpr(f, bv1, BvExtractExpr(bv2, 31, 0))
    
    print EqExpr(BvZeroExtend(bv1, 64), bv2)

if __name__=="__main__":
    test()
