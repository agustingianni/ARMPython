'''
Expressions
    BoolExpr
        have pythonic methods for all typical boolean operations
    BVExpr
        have pythonic method for BV operations.
        it never adapts the size of the expression by itself
    
    Once created, the expression should be considered immutable.
    __init__ functions should be avoided as much as possible.
    All type information should be static and part of the class definition.

TODO:
  Common subexpression cancellation
  Associative and commutative rules optimization. ej:
    (x + x) + x == x * 3       [find a constructive way for this]
  
'''

import math

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
            #p & p <=> p
            if self.__hash__() == other.__hash__():
                return self
            
            #p & !p <=> False
            if (isinstance(self, BoolNotExpr) and self.children[0].__hash__() == other.__hash__()) or \
               (isinstance(other, BoolNotExpr) and other.children[0].__hash__() == self.__hash__()):
                return False
                
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
            #p | p <=> p
            if self.__hash__() == other.__hash__():
                return self
            
            #p | !p <=> True
            if (isinstance(self, BoolNotExpr) and self.children[0].__hash__() == other.__hash__()) or \
               (isinstance(other, BoolNotExpr) and other.children[0].__hash__() == self.__hash__()):
                return True
            
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
            #p ^ p <=> False
            if self.__hash__() == other.__hash__():
                return False
            
            #p ^ !p <=> True
            if (isinstance(self, BoolNotExpr) and self.children[0].__hash__() == other.__hash__()) or \
               (isinstance(other, BoolNotExpr) and other.children[0].__hash__() == self.__hash__()):
                return True

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
            #!!p = p
            if isinstance(self, BoolNotExpr):
                return self.children[0]
            return BoolNotExpr(self)
    
    def __rshift__(self, other):
        #using >> for Implication

        #p -> q <=> !p | q
        return ~self | other
    
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
                
            #a EQ a <=> True
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

            #a NE a <=> False
            if self.__hash__() == other.__hash__():
                return False
            return DistinctExpr(self, other)



class BvExpr(Expr):
    __base_sort__="BitVec"
    
    def __nonzero__(self):
        raise Exception, "A BitVector Expression cannot be evaluated to boolean"
    
    def __len__(self):
        return self.size

    def __and__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            #p & p = p
            if self.__hash__() == other.__hash__():
                return self
            
            #p & !p = 0
            if (isinstance(self, BvNotExpr) and self.children[0].__hash__() == other.__hash__()) or \
               (isinstance(other, BvNotExpr) and other.children[0].__hash__() == self.__hash__()):
                return 0

            return BvAndExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvAndExpr(self, other)

    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            #p | p = p
            if self.__hash__() == other.__hash__():
                return self
            
            #p | !p = all-1
            if (isinstance(self, BvNotExpr) and self.children[0].__hash__() == other.__hash__()) or \
               (isinstance(other, BvNotExpr) and other.children[0].__hash__() == self.__hash__()):
                return self.size_mask
            
            return BvOrExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvOrExpr(self, other)

    def __ror__(self, other):
        return self.__or__(other)
    
    def __xor__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            #p ^ p = 0
            if self.__hash__() == other.__hash__():
                return 0

            #p ^ !p = all-1
            if (isinstance(self, BvNotExpr) and self.children[0].__hash__() == other.__hash__()) or \
               (isinstance(other, BvNotExpr) and other.children[0].__hash__() == self.__hash__()):
                return self.size_mask
            
            return BvXorExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvXorExpr(self, other)

    def __rxor__(self, other):
        return self.__xor__(other)
    
    def __invert__(self):
        if self.__has_value__:
            return (~self.value) & self.size_mask
        else:
            #!!p = p
            if isinstance(self, BvNotExpr):
                return self.children[0]
            return BvNotExpr(self)
    
    def __neg__(self):
        if self.__has_value__:
            return (-self.value) & self.size_mask
        else:
            #-(-a) = a
            if isinstance(self, BvNegExpr):
                return self.children[0]
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
                    
                    #p >> 0 = p
                    if other_value == 0:
                        return self
                    
                    #p >> size(p) = 0
                    if other_value == self.size:
                        return 0
                    
                    #p >> n = concat(const-0(n), extract(p, size(p)-1, n))
                    return BvConstExpr(0, other_value).concat(self.extract(self.size - 1, other_value))
                
                # 0 >> p = 0
                elif self.value == 0:
                    return 0

                return BvShrExpr(self, other)

    def __rrshift__(self, other):
        if self.__has_value__:
            return (other >> self.value) & self.size_mask
        else:
            # 0 >> p = 0
            if other == 0:
                return 0
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
                    
                    #p << 0 = p
                    if other_value == 0:
                        return self
                    
                    #p << size(p) = 0
                    if other_value == self.size:
                        return 0
                    
                    #p << n = concat(extract(p, size(p)-1-n, 0), const-0(n))
                    return self.extract(self.size - 1 - other_value, 0).concat(BvConstExpr(0, other_value))
                
                # 0 << p = 0
                elif self.value == 0:
                    return 0

                return BvShlExpr(self, other)

    def __rlshift__(self, other):
        if self.__has_value__:
            return (other << self.value) & self.size_mask
        else:
            # 0 << p = 0
            if other == 0:
                return 0
            return BvShlExpr(BvConstExpr(other, self.size), self)

    def __add__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            if self.__hash__() == other.__hash__():
                #p + p = p * 2 = p << 1
                return self << 1
            
            #p + (-p) == 0
            if (isinstance(self, BvNegExpr) and self.children[0].__hash__() == other.__hash__()) or \
               (isinstance(other, BvNegExpr) and other.children[0].__hash__() == self.__hash__()):
                return 0
            return BvAddExpr(self, other)
        else:
            (value, secondary, both_values) = self.getValue(other)
            if both_values:
                return (value + secondary) & self.size_mask
            else:
                #p + 0 = p
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
            #p - p = 0
            if self.__hash__() == other.__hash__():
                return 0
            
            #p - (-p) = p + p = p * 2
            #(-p) - p = (-p) * 2
            if (isinstance(self, BvNegExpr) and self.children[0].__hash__() == other.__hash__()) or \
              (isinstance(other, BvNegExpr) and other.children[0].__hash__() == self.__hash__()):
                return self * 2
            
            return BvSubExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvSubExpr(self, other)

    def __rsub__(self, other):
        if self.__has_value__:
            return (other - self.value) & self.size_mask
        else:
            #0 - p = -p
            if other == 0:
                return -self

            return BvSubExpr(BvConstExpr(other, self.size), self)

    def __div__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            
            #p / p = 1
            if self.__hash__() == other.__hash__():
                return 1
            
            #p / (-p) = -1
            if (isinstance(self, BvNegExpr) and self.children[0].__hash__() == other.__hash__()) or \
              (isinstance(other, BvNegExpr) and other.children[0].__hash__() == self.__hash__()):
                return -1
            
            return BvUDivExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvUDivExpr(self, other)

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
                    other=BvConstExpr(other, self.size)
                    
                return BvMulExpr(self, other)

    def __rmul__(self, other):
        return self.__mul__(other)

    def __mod__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            #p mod p = 0
            if self.__hash__() == other.__hash__():
                return 0

            return BvURemExpr(self, other)
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
                        return BvConstExpr(0, long(l)).concat(self.extract(long(l) - 1, 0))
                else:
                    #0 mod p = 0
                    if self.value == 0:
                        return 0

                if not other_is_expr:
                    other=BvConstExpr(other, self.size)
                    
                return BvURemExpr(self, other)

    def __rmod__(self, other):
        if self.__has_value__:
            return (other % self.value) & self.size_mask
        else:
            #0 mod p = 0
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
            
            #p EQ p <=> True
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
            
            #p NE p <=> False
            if self.__hash__() == other.__hash__():
                return False
            return DistinctExpr(self, other)

    def __gt__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            
            #p > p <=> False
            if self.__hash__() == other.__hash__():
                return False
            return BvUgtExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvUgtExpr(self, other)

    def __ge__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:

            #p >= p <=> True
            if self.__hash__() == other.__hash__():
                return True
            return BvUgeExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvUgeExpr(self, other)

    def __lt__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:

            #p < p <=> False
            if self.__hash__() == other.__hash__():
                return False
            return BvUltExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvUltExpr(self, other)

    def __le__(self, other):
        other_is_expr=isinstance(other, BvExpr)
        if other_is_expr and not other.__has_value__ and not self.__has_value__:
            
            #p <= p <=> True
            if self.__hash__() == other.__hash__():
                return True
            return BvUleExpr(self, other)
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
                    other=BvConstExpr(other, self.size)
                    
                return BvUgeExpr(self, other)
    

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
                return BvConcatExpr(c0.children[0], newchild, force_assoc=False).extract(end, start)

        #common case        
        return BvExtractExpr(self, end, start)
    
    def concat(self, other, force_expr=False):
        assert isinstance(other, BvExpr) #otherwise the result is unpredictable

        if self.__has_value__ and other.__has_value__:
            val = self.value << other.size | other.value
            return BvConstExpr(val, self.size + other.size) if force_expr else val
        
        if isinstance(self, BvExtractExpr) and isinstance(other, BvExtractExpr) and \
           self.children[0].__hash__() == other.children[0].__hash__():
            
            #concat(extract(x, a, j), extract(x, j-1, b)) = extract(x, a, b)
            if other.end == self.start - 1:
                return self.children[0].extract(self.end, other.start)
        
        return BvConcatExpr(self, other)

    def zeroExtend(self, new_size):
        assert self.size <= new_size
        if self.size == new_size:
            return self
        
        return BvConstExpr(0, new_size - self.size).concat(self)
    
    def signExtend(self, new_size):
        assert self.size <= new_size
        if self.size == new_size:
            return self
        
        extension_size = new_size - self.size
        
        sign_bit=self.extract(self.size-1, self.size-1)
        extension=IteExpr(sign_bit == 1, BvConstExpr(2 ** extension_size - 1, extension_size), BvConstExpr(0, extension_size))
        if not isinstance(extension, BvExpr):
            extension=BvConstExpr(extension, extension_size)
        return extension.concat(self)

# Raw Expressions

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
        assert p1.__sort__ == p2.__sort__
        self.children=(p1, p2)

class DistinctExpr(BoolExpr):
    __function__="distinct"
    __commutative__=True
    def __init__(self, p1, p2):
        assert p1.__sort__ == p2.__sort__
        self.children=(p1, p2)

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
    def __init__(self, p1, p2, force_assoc = True):
        #Force associativity to the left
        if force_assoc and isinstance(p2, BvConcatExpr):
            p1 = p1.concat(p2.children[0], force_expr=True)
            p2 = p2.children[1]

        self.children=(p1, p2)
        self.size=p1.size + p2.size
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__="BitVec %d" % self.size

class BvExtractExpr(BvExpr):
    __function__="extract"
    def __init__(self, p1, i, j):
        assert p1.size > i >= j >= 0

        self.children=(p1, )
        
        #start and end both include the boundaries
        self.start = j
        self.end = i
        self.size=i - j + 1
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__="BitVec %d" % self.size

    def __str__(self):
        return "%s(%s, %d, %d)" % (self.__function__, str(self.children[0]), self.end, self.start)

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
    def __init__(self, p1, p2, force_assoc=True):
        assert p1.size == p2.size

        #float constants to the right
        if isinstance(p1, BvConstExpr):
            tmp = p2
            p2 = p1
            p1 = tmp

        #Force associativity to the right
        #(a * b) * c   <=>   a * (b * c)
        #   p1     p2
        if force_assoc and isinstance(p1, BvAndExpr):
            p2 = p2.__and__(p1.children[1]) #b * c
            p2 = BvConstExpr(p2, p1.size) if not isinstance(p2, BvExpr) else p2
            p1 = p1.children[0] #a

        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvOrExpr(BvExpr):
    __function__="bvor"
    __commutative__=True
    def __init__(self, p1, p2, force_assoc=True):
        assert p1.size == p2.size

        #float constants to the right
        if isinstance(p1, BvConstExpr):
            tmp = p2
            p2 = p1
            p1 = tmp

        #Force associativity to the right
        #(a * b) * c   <=>   a * (b * c)
        #   p1     p2
        if force_assoc and isinstance(p1, BvOrExpr):
            p2 = p2.__or__(p1.children[1]) #b * c
            p2 = BvConstExpr(p2, p1.size) if not isinstance(p2, BvExpr) else p2
            p1 = p1.children[0] #a

        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvXorExpr(BvExpr):
    __function__="bvxor"
    __commutative__=True
    def __init__(self, p1, p2, force_assoc=True):
        assert p1.size == p2.size

        #float constants to the right
        if isinstance(p1, BvConstExpr):
            tmp = p2
            p2 = p1
            p1 = tmp

        #Force associativity to the right
        #(a * b) * c   <=>   a * (b * c)
        #   p1     p2
        if force_assoc and isinstance(p1, BvXorExpr):
            p2 = p2.__xor__(p1.children[1]) #b * c
            p2 = BvConstExpr(p2, p1.size) if not isinstance(p2, BvExpr) else p2
            p1 = p1.children[0] #a

        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvAddExpr(BvExpr):
    __function__="bvadd"
    __commutative__=True
    def __init__(self, p1, p2, force_assoc = True):
        assert p1.size == p2.size

        #float constants to the right
        if isinstance(p1, BvConstExpr):
            tmp = p2
            p2 = p1
            p1 = tmp

        #Force associativity to the right
        #(a + b) + c   <=>   a + (b + c)
        #   p1     p2
        if force_assoc and isinstance(p1, BvAddExpr):
            p2 = p2.__add__(p1.children[1]) #b + c
            p2 = BvConstExpr(p2, p1.size) if not isinstance(p2, BvExpr) else p2
            p1 = p1.children[0] #a

        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvSubExpr(BvExpr):
    __function__="bvsub"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvMulExpr(BvExpr):
    __function__="bvmul"
    __commutative__=True
    def __init__(self, p1, p2, force_assoc=True):
        assert p1.size == p2.size

        #float constants to the right
        if isinstance(p1, BvConstExpr):
            tmp = p2
            p2 = p1
            p1 = tmp

        #Force associativity to the right
        #(a * b) * c   <=>   a * (b * c)
        #   p1     p2
        if force_assoc and isinstance(p1, BvMulExpr):
            p2 = p2.__mul__(p1.children[1]) #b * c
            p2 = BvConstExpr(p2, p1.size) if not isinstance(p2, BvExpr) else p2
            p1 = p1.children[0] #a

        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvUDivExpr(BvExpr):
    __function__="bvudiv"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvURemExpr(BvExpr):
    __function__="bvurem"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__
    
class BvShlExpr(BvExpr):
    __function__="bvshl"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

class BvShrExpr(BvExpr):
    __function__="bvshr"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)
        self.size=p1.size
        self.size_mask=p1.size_mask
        self.__sort__=p1.__sort__

# Comparison (return Bool from 2 BitVec)

class BvUltExpr(BoolExpr):
    __function__="bvult"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)

class BvUleExpr(BoolExpr):
    __function__="bvule"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)

class BvUgtExpr(BoolExpr):
    __function__="bvugt"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)

class BvUgeExpr(BoolExpr):
    __function__="bvuge"
    def __init__(self, p1, p2):
        assert p1.size == p2.size
        self.children=(p1, p2)


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
    bv2=BvVarExpr(32, "bv2")
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
    
    print "%x" % bv1.extract(15,0)
    print bv2.extract(15,0)
    print "%x" % bv1.concat(BvConstExpr(0xde, 8))
    print bv1.concat(bv2)
    print bv2.extract(31,0)
    
    c1=BvVarExpr(8, "c1")
    c2=BvVarExpr(8, "c2")
    c3=BvVarExpr(8, "c3")
    c4=BvVarExpr(8, "c4")
    w1=BvVarExpr(16, "w1")
    d1=BvVarExpr(32, "d1")
    
    d2=c1.concat(c2.concat(c3.concat(c4)))
    print d2
    d2=c1.concat(c2).concat(c3).concat(c4)
    print d2
    d2=c1.concat(c2).concat(c3.concat(c4))
    print d2
    print d2 >> 16
    print d2 << 24
    
    print "================================"
    
    for offset in (0, 8, 16, 24):
        for size in (8, 16, 24):
            if size + offset > 32:
                continue
            print "***********************"
            print "end=%d, start=%d" % (size+offset-1, offset) 
            out=d2.extract(size+offset-1,offset)
            if isinstance(out, BvExtractExpr):
                print d2
                print out
                     
    print "================================"
    print bv2 + (-bv2)
    print d2 % 0x10000

    print "%x" % bv1.signExtend(64)
    print bv2.signExtend(64)

    print "%x" % bv1.zeroExtend(64)
    print bv2.zeroExtend(64)
    
    print "================================"
    print bv1 + ((bv2 + bv1) + bv2)
    print (bv1 + bv2) + bv1

    print "================================"
    print bv2 * 3 * 5
    print 3 * bv2 * 5 * bv2 * 7

if __name__=="__main__":
    test()
