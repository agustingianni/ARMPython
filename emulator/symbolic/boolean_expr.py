from emulator.symbolic.base_expr import Expr

class BoolExpr(Expr):
    __sort__="Bool"
    
    def __and__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            return BoolAndExpr.construct(self, other)
        else:
            (value, secondary, _) = self.getValue(other)
            #p & T <=> p, p & F <=> F
            return secondary if value else False

    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            return BoolOrExpr.construct(self, other)
        else:
            (value, secondary, _) = self.getValue(other)
            #p | T <=> T, p | F <=> p
            return True if value else secondary

    def __ror__(self, other):
        return self.__or__(other)
    
    def __xor__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            return BoolXorExpr.construct(self, other)
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
            return BoolNotExpr.construct(self)
    
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
                
            return EqExpr.construct(self, other)

    def __ne__(self, other):
        other_is_expr = isinstance(other, BoolExpr)
        if self.__has_value__ and (not other_is_expr or other.__has_value__):
            return self.value != bool(other)
        else:
            if not other_is_expr:
                other = TrueExpr if bool(other) else FalseExpr

            return DistinctExpr.construct(self, other)

    def ite(self, _then, _else):
        from emulator.symbolic.misc_expr import IteExpr
        return IteExpr(self, _then, _else)

class BoolVarExpr(BoolExpr):
    children=()
    value=None
    __depth__=1
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
    __depth__=1
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
    __depth__=1
    def __str__(self):
        return self.__function__
    def __nonzero__(self):
        return False
FalseExpr=_FalseExpr() #singleton

class BoolAndExpr(BoolExpr):
    __function__="and"
    __commutative__=True
    __python_op__=staticmethod(BoolExpr.__and__)
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
    
    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p & p <=> p
        if p1.__hash__() == p1.__hash__():
            return p1
        
        #p & !p <=> False
        if (isinstance(p1, BoolNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BoolNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return False if not force_expr else FalseExpr
        return BoolAndExpr(p1, p2)

class BoolOrExpr(BoolExpr):
    __function__="or"
    __commutative__=True
    __python_op__=staticmethod(BoolExpr.__or__)
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p | p <=> p
        if p1.__hash__() == p1.__hash__():
            return p1
        
        #p | !p <=> True
        if (isinstance(p1, BoolNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BoolNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return True if not force_expr else TrueExpr
        return BoolOrExpr(p1, p2)

class BoolXorExpr(BoolExpr):
    __function__="xor"
    __commutative__=True
    __python_op__=staticmethod(BoolExpr.__xor__)
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p ^ p <=> False
        if p1.__hash__() == p1.__hash__():
            return False if not force_expr else FalseExpr
        
        #p ^ !p <=> True
        if (isinstance(p1, BoolNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BoolNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return True if not force_expr else TrueExpr
        return BoolXorExpr(p1, p2)

class BoolNotExpr(BoolExpr):
    __function__="not"
    __python_op__=staticmethod(BoolExpr.__invert__)
    def __init__(self, p1):
        self.__depth__=p1.__depth__ + 1
        self.children=(p1, )

    @staticmethod
    def construct(p1, force_expr=False):
        #!!p = p
        if isinstance(p1, BoolNotExpr):
            return p1.children[0]
        
        return BoolNotExpr(p1)

class BoolImplExpr(BoolExpr):
    __function__="=>"
    __python_op__=staticmethod(BoolExpr.__rshift__)
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)

class EqExpr(BoolExpr):
    __function__="="
    __commutative__=True
    def __init__(self, p1, p2):
        assert p1.__sort__ == p2.__sort__
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
    
    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p EQ p <=> True
        if p1.__hash__() == p2.__hash__():
            return True if not force_expr else TrueExpr
        return EqExpr(p1, p2)

class DistinctExpr(BoolExpr):
    __function__="distinct"
    __commutative__=True
    def __init__(self, p1, p2):
        assert p1.__sort__ == p2.__sort__
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p NE p <=> False
        if p1.__hash__() == p2.__hash__():
            return False if not force_expr else FalseExpr
        return DistinctExpr(p1, p2)

class BoolIteExpr(BoolExpr):
    __function__="ite"
    def __init__(self, _if, _then, _else):
        assert isinstance(_if, BoolExpr)
        assert _then.__sort__ == _else.__sort__
        self.__depth__=max(_if.__depth__, _then.__depth__, _else.__depth__) + 1
        self.children=(_if, _then, _else)
