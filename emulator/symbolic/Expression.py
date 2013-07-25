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
    __commutative__=False
    __hashcode__=None

    def __repr__(self):
        return "<%s>" % self

    def __str__(self):
        children_repr=[str(x) for x in self.children]
        return "%s(%s)" % (self.__function__, ", ".join(children_repr))

    def export(self, fmt="smtlib2"):
        pass

    def getValue(self, val):
        """
        it's assumed that one of the two element does have a value.
        
        returns (value, secondary_value_or_expr, bool_are_both_values)
        
        DO NOT USE THIS ON NON-CONMUTATIVE OPERATIONS
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

    def __hash__(self):
        if self.__hashcode__ != None:
            return self.__hashcode__

        children=[hash(x) for x in self.children]
        if self.__commutative__:
            children.sort()
        children=tuple(children)

        optional=[]
        if self.__has_value__:
            optional.append(self.value)
        if hasattr(self, "name"):
            optional.append(self.name)
        if hasattr(self, "__function__"):
            optional.append(self.__function__)

        self.__hashcode__ = hash((self.__sort__, self.__has_value__, tuple(optional), children))
        return self.__hashcode__

# Boolean sort and functions    
class BoolExpr(Expr):
    __sort__="Bool"
    
    def __and__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return self
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
            if self.__hash__() == other.__hash__():
                return self
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
            if self.__hash__() == other.__hash__():
                return False
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
    
    def __rshift__(self, other):
        #using >> for Implication

        other_is_expr = isinstance(other, BoolExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return True
            return BoolImplExpr(self, other)
        else:
            if not other_is_expr or other.__has_value__:
                #p => T <=> T, p => F <=> ~p
                #~self is simplified on the check for __has_value__ in __invert__
                return True if bool(other) else ~self
            else:
                return BoolImplExpr(self, other)
    
    def __rrshift__(self, other):
        #This is only for the reversed case of implication
        #other is never an expression.

        #T => p <=> p, F => p <=> T
        if self.__has_value__:
            return self.value if bool(other) else True
        else:
            return self if bool(other) else True
    
    def __eq__(self, other):
        other_is_expr = isinstance(other, BoolExpr)
        if self.__has_value__ and (not other_is_expr or other.__has_value__):
            return self.value == bool(other)
        else:
            if not other_is_expr:
                other = TrueExpr if bool(other) else FalseExpr
            if self.__hash__() == other.__hash__():
                return True
            return EqExpr(self, other)

    def __ne__(self, other):
        other_is_expr = isinstance(other, BoolExpr)
        if self.__has_value__ and (not other_is_expr or other.__has_value__):
            return self.value != bool(other)
        else:
            if not other_is_expr:
                other = TrueExpr if bool(other) else FalseExpr
            if self.__hash__() == other.__hash__():
                return False
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
    __commutative__=True
    def __init__(self, p1, p2):
        self.children=(p1, p2)

class BoolOrExpr(BoolExpr):
    __function__="or"
    __commutative__=True
    def __init__(self, p1, p2):
        self.children=(p1, p2)

class BoolXorExpr(BoolExpr):
    __function__="xor"
    __commutative__=True
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
    __commutative__=True
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        assert p1.__sort__ == p2.__sort__

class DistinctExpr(BoolExpr):
    __function__="distinct"
    __commutative__=True
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
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return self
            return BvAndExpr(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return value & secondary
            else:
                if value == 0:
                    return 0
                
                if value == self.size_mask:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvAndExpr(self, other)

    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return self
            return BvOrExpr(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value | secondary) & self.size_mask
            else:
                if value == 0:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask
                
                if value == self.size_mask:
                    return self.size_mask

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvOrExpr(self, other)

    def __ror__(self, other):
        return self.__or__(other)
    
    def __xor__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return 0
            return BvXorExpr(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value ^ secondary) & self.size_mask
            else:
                if value == 0:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask
                
                if value == self.size_mask:
                    return ~secondary if isinstance(secondary, BvExpr) else (~secondary) & self.size_mask

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvXorExpr(self, other)

    def __rxor__(self, other):
        return self.__xor__(other)
    
    def __invert__(self):
        if self.__has_value__:
            return (~self.value) & self.size_mask
        else:
            return BvNotExpr(self)
    
    def __neg__(self):
        if self.__has_value__:
            return (-self.value) & self.size_mask
        else:
            return BvNegExpr(self)
    
    def __rshift__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvShrExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or other.__has_value__):
                return self.value >> long(other)
            else:
                if not self.__has_value__:
                    other_value=long(other)
                    if other_value == 0:
                        return self
                    if other_value == self.size:
                        return 0
                elif self.value == 0:
                    return 0

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvShrExpr(self, other)

    def __rrshift__(self, other):
        if self.__has_value__:
            return (other >> self.value) & self.size_mask
        else:
            return BvShrExpr(BvConstExpr(other, self.size), self)
    
    def __lshift__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvShlExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or other.__has_value__):
                return (self.value << long(other)) & self.size_mask
            else:
                if not self.__has_value__:
                    other_value=long(other)
                    if other_value == 0:
                        return self
                    if other_value == self.size:
                        return 0
                elif self.value == 0:
                    return 0

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvShlExpr(self, other)

    def __rlshift__(self, other):
        if self.__has_value__:
            return (other << self.value) & self.size_mask
        else:
            return BvShlExpr(BvConstExpr(other, self.size), self)

    def __add__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                #a + a = a * 2 = a << 1
                return BvShlExpr(self, BvConstExpr(1, self.size)) #meta-optimization... yay!
            return BvAddExpr(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value + secondary) & self.size_mask
            else:
                if value == 0:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask
                
                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvAddExpr(self, other)

    def __radd__(self, other):
        return self.__add__(other)

    def __sub__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return 0
            return BvSubExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or other.__has_value__):
                return (self.value - long(other)) & self.size_mask
            else:
                if not self.__has_value__ and long(other) == 0:
                    return self
                
                if self.__has_value__ and self.value == 0:
                    return -other if other_is_expr else (-other) & self.size_mask

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvSubExpr(self, other)

    def __rsub__(self, other):
        if self.__has_value__:
            return (other - self.value) & self.size_mask
        else:
            if other == 0:
                return -self

            return BvSubExpr(BvConstExpr(other, self.size), self)

    def __div__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return 1
            return BvUDivExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return (self.value / long(other)) & self.size_mask
            else:
                if not self.__has_value__ and long(other) == 0:
                    raise ZeroDivisionError

                if self.__has_value__ and self.value == 0:
                    return 0

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvUDivExpr(self, other)

    def __rdiv__(self, other):
        if self.__has_value__:
            return (other / self.value) & self.size_mask
        else:
            if other == 0:
                return 0

            return BvUDivExpr(BvConstExpr(other, self.size), self)

    def __mul__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            return BvMulExpr(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value * secondary) & self.size_mask
            else:
                if value == 0:
                    return 0

                if value == 1:
                    return secondary if isinstance(secondary, BvExpr) else secondary & self.size_mask

                if value == self.size_mask:
                    return -secondary if isinstance(secondary, BvExpr) else (-secondary) & self.size_mask
                
                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvMulExpr(self, other)

    def __rmul__(self, other):
        return self.__mul__(other)

    def __mod__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return 0
            return BvURemExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return (self.value % long(other)) & self.size_mask
            else:
                if not self.__has_value__ and long(other) == 0:
                    raise ZeroDivisionError

                if self.__has_value__ and self.value == 0:
                    return 0

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvURemExpr(self, other)

    def __rmod__(self, other):
        if self.__has_value__:
            return (other % self.value) & self.size_mask
        else:
            if other == 0:
                return 0

            return BvURemExpr(BvConstExpr(other, self.size), self)

    def __eq__(self, other):
        other_is_expr = isinstance(other, BvExpr)
        if self.__has_value__ and (not other_is_expr or other.__has_value__):
            return self.value == long(other)
        else:
            if not other_is_expr:
                other = BvConstExpr(other, self.size)
            if self.__hash__() == other.__hash__():
                return True
            return EqExpr(self, other)

    def __ne__(self, other):
        other_is_expr = isinstance(other, BvExpr)
        if self.__has_value__ and (not other_is_expr or other.__has_value__):
            return self.value != long(other)
        else:
            if not other_is_expr:
                other = BvConstExpr(other, self.size)
            if self.__hash__() == other.__hash__():
                return False
            return DistinctExpr(self, other)

    def __gt__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return False
            return BvUgtExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value > (long(other) & self.size_mask)
            else:
                #0 > X <=> False
                #X > size_mask <=> False
                if self.__has_value__ and self.value == 0:
                    return False
                if not self.__has_value__ and long(other) == self.size_mask:
                    return False

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvUgtExpr(self, other)

    def __ge__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return True
            return BvUgeExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value >= (long(other) & self.size_mask)
            else:
                #size_mask >= X <=> True
                #X >= 0 <=> True
                if self.__has_value__ and self.value == self.size_mask:
                    return True
                if not self.__has_value__ and long(other) == 0:
                    return True

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvUgeExpr(self, other)

    def __lt__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return False
            return BvUltExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value < (long(other) & self.size_mask)
            else:
                #size_mask < X <=> False
                #X < 0 <=> False
                if self.__has_value__ and self.value == self.size_mask:
                    return False
                if not self.__has_value__ and self.value == 0:
                    return False

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvUltExpr(self, other)

    def __le__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                return True
            return BvUleExpr(self, other)
        else:
            if self.__has_value__ and (not other_is_expr or \
                other.__has_value__):
                return self.value <= (long(other) & self.size_mask)
            else:
                #X <= size_mask <=> True
                #0 <= X <=> True
                if self.__has_value__ and self.value == 0:
                    return True
                if not self.__has_value__ and long(other) == self.size_mask:
                    return True

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvUgeExpr(self, other)

class BvConstExpr(BvExpr):
    children=()
    __has_value__=True
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

class BvVarExpr(BvExpr):
    children=()
    value=None
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

class BvConcatExpr(BvExpr):
    __function__="concat"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size + p2.size
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__="BitVec %d" % self.size

class BvExtractExpr(BvExpr):
    __function__="extract"
    def __init__(self, p1, i, j):
        self.children=(p1, )
        
        #start and end both include the boundaries
        self.start = j
        self.end = i
        self.size=i - j + 1
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__="BitVec %d" % self.size
        assert p1.size > i >= j >= 0

class BvNotExpr(BvExpr):
    __function__="bvnot"
    def __init__(self, p1):
        self.children=(p1, )
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvNegExpr(BvExpr):
    __function__="bvneg"
    def __init__(self, p1):
        self.children=(p1, )
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvAndExpr(BvExpr):
    __function__="bvand"
    __commutative__=True
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvOrExpr(BvExpr):
    __function__="bvor"
    __commutative__=True
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvXorExpr(BvExpr):
    __function__="bvxor"
    __commutative__=True
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvAddExpr(BvExpr):
    __function__="bvadd"
    __commutative__=True
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvSubExpr(BvExpr):
    __function__="bvsub"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvMulExpr(BvExpr):
    __function__="bvmul"
    __commutative__=True
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvUDivExpr(BvExpr):
    __function__="bvudiv"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvURemExpr(BvExpr):
    __function__="bvurem"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size
    
class BvShlExpr(BvExpr):
    __function__="bvshl"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
        assert p1.size == p2.size

class BvShrExpr(BvExpr):
    __function__="bvshr"
    def __init__(self, p1, p2):
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
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
        self.size=_then.size
        self.size_mask=_then.size_mask
        self.__sort__=_then.__sort__
        self.children=(_if, _then, _else)

class _BoolIteExpr(BoolExpr):
    __function__="ite"
    def __init__(self, _if, _then, _else):
        assert isinstance(_if, BoolExpr)
        assert _then.__sort__ == _else.__sort__
        self.children=(_if, _then, _else)

def IteExpr(_if, _then, _else, op_size=32):
    if isinstance(_if, BoolExpr) and not _if.__has_value__:
        if not isinstance(_then, Expr):
            if isinstance(_then, bool):
                _then=TrueExpr if _then else FalseExpr
            else:
                if isinstance(_else, BvExpr):
                    _then=BvConstExpr(_then, _else.size)
                else:
                    _then=BvConstExpr(_then, op_size)
    
        if not isinstance(_else, Expr):
            if isinstance(_else, bool):
                _else=TrueExpr if _else else FalseExpr
            else:
                if isinstance(_then, BvExpr):
                    _else=BvConstExpr(_else, _then.size)
                else:
                    _else=BvConstExpr(_else, op_size)

        #if _then == _else it doesn't matter what _if says
        (value, secondary, both_values) = _then.getValue(_else)
        if both_values and value == secondary:
            return value

        if isinstance(_then, BoolExpr):
            return _BoolIteExpr(_if, _then, _else)
        else:
            return _BvIteExpr(_if, _then, _else)
    else:
        if bool(_if):
            return _then.value if isinstance(_then, Expr) and _then.__has_value__ else _then
        else:
            return  _else.value if isinstance(_else, Expr) and _else.__has_value__ else _else


def test():
    bv1=BvConstExpr(0xcafecafe, 32)
    bv2=BvVarExpr(32)
    anded=(((bv1 & bv2) | 0x12345678) + 0xbababebe)
    anded2=(0xbababebe + (0x12345678 | (bv2 & bv1)))
    
    print hash(bv1)
    print hash(bv2)
    print hash(anded)
    print hash(anded2)
    d={}
    d[bv1]="bv1"
    d[bv2]="bv2"
    d[anded]="anded"
    print repr(d)
    d[anded2]="anded2"
    print repr(d)
    
    print bv2 == bv1
    print bv2 == bv2
    print bv2 + bv2
    print bv2 & bv2
    print bv2 ^ bv2


if __name__=="__main__":
    test()
