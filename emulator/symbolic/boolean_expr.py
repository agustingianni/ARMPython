from emulator.symbolic.base_expr import Expr
from utils.lru import LruCache

class BoolExpr(Expr):
    __slots__=()
    __sort__="Bool"

    def __nonzero__(self):
        if self.__has_value__:
            return self.value

        raise Exception, "A non-constant Boolean Expression cannot be evaluated to boolean"
    
    def __and__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            return BoolAndExpr.construct(self, other)
        else:
            (value, secondary, _) = self.getValue(other)
            #p & T <=> p (Identity), p & F <=> F (Annihilator)
            return secondary if value else False

    def __rand__(self, other):
        return self.__and__(other)
    
    def __or__(self, other):
        if isinstance(other, BoolExpr) and not other.__has_value__ \
            and not self.__has_value__:
            return BoolOrExpr.construct(self, other)
        else:
            (value, secondary, _) = self.getValue(other)
            #p | T <=> T (Annihilator), p | F <=> p (Identity)
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
    __slots__=("name")
    children=()
    value=None
    __depth__=1
    __backend_fun__=lambda: None
    def __init__(self, name=None):
        if name == None:
            self.name = "bool_%x" % id(self)
        else:
            self.name=name
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    def __str__(self):
        return self.name

    def __export__(self):
        return self.name 
    
    def __hash_fun__(self):
        hashcode = hash((self.__sort__, "var", self.name))
        self.__hash__ = lambda: hashcode
        return hashcode

    def extractVariables(self):
        return (self, )

    @staticmethod
    def construct(name=None):
        return BoolVarExpr(name)

class _TrueExpr(BoolExpr):
    __slots__=()
    __function__="true"
    children=()
    __has_value__=True
    value=True
    __depth__=1
    def __str__(self):
        return self.__function__
    def __nonzero__(self):
        return True
TrueExpr=_TrueExpr() #single instance used everywhere as it's immutable
#precalculate hash for this singletons
TrueExpr.__hash_fun__()

class _FalseExpr(BoolExpr):
    __slots__=()
    __function__="false"
    children=()
    __has_value__=True
    value=False
    __depth__=1
    def __str__(self):
        return self.__function__
    def __nonzero__(self):
        return False
FalseExpr=_FalseExpr() #instance used everywhere as it's immutable
#precalculate hash for this singletons
FalseExpr.__hash_fun__()

class BoolAndExpr(BoolExpr):
    __slots__=()
    __function__="and"
    __commutative__=True
    __python_op__=staticmethod(BoolExpr.__and__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @staticmethod
    def construct(p1, p2, force_expr=False):
        p1h = p1.__hash__()
        p2h = p2.__hash__()
        
        #p & p <=> p. Idempotence.
        if p1h == p2h:
            return p1

        #p & (p | q) <=> p. Absorption.
        if (isinstance(p2, BoolOrExpr) and (p2.children[0].__hash__() == p1h or p2.children[1].__hash__() == p1h)):
            return p1

        #(p | q) & p <=> p. Absorption.
        if (isinstance(p1, BoolOrExpr) and (p1.children[0].__hash__() == p2h or p1.children[1].__hash__() == p2h)):
            return p2
        
        #p & !p <=> False. Complementation.
        if (isinstance(p1, BoolNotExpr) and p1.children[0].__hash__() == p2h) or \
           (isinstance(p2, BoolNotExpr) and p2.children[0].__hash__() == p1h):
            return False if not force_expr else FalseExpr
        return BoolAndExpr(p1, p2)

class BoolOrExpr(BoolExpr):
    __slots__=()
    __function__="or"
    __commutative__=True
    __python_op__=staticmethod(BoolExpr.__or__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2, force_expr=False):
        p1h = p1.__hash__()
        p2h = p2.__hash__()

        #p | p <=> p. Idempotence.
        if p1h == p2h:
            return p1
        
        #p | (p & q) <=> p. Absorption.
        if (isinstance(p2, BoolAndExpr) and (p2.children[0].__hash__() == p1h or p2.children[1].__hash__() == p1h)):
            return p1

        #(p & q) | p <=> p. Absorption.
        if (isinstance(p1, BoolAndExpr) and (p1.children[0].__hash__() == p2h or p1.children[1].__hash__() == p2h)):
            return p2

        #p | !p <=> True. Complementation.
        if (isinstance(p1, BoolNotExpr) and p1.children[0].__hash__() == p2h) or \
           (isinstance(p2, BoolNotExpr) and p2.children[0].__hash__() == p1h):
            return True if not force_expr else TrueExpr
        return BoolOrExpr(p1, p2)

class BoolXorExpr(BoolExpr):
    __slots__=()
    __function__="xor"
    __commutative__=True
    __python_op__=staticmethod(BoolExpr.__xor__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p ^ p <=> False. Idempotence.
        if p1.__hash__() == p2.__hash__():
            return False if not force_expr else FalseExpr
        
        #p ^ !p <=> True. Complementation.
        if (isinstance(p1, BoolNotExpr) and p1.children[0].__hash__() == p2.__hash__()) or \
           (isinstance(p2, BoolNotExpr) and p2.children[0].__hash__() == p1.__hash__()):
            return True if not force_expr else TrueExpr
        return BoolXorExpr(p1, p2)

class BoolNotExpr(BoolExpr):
    __slots__=()
    __function__="not"
    __python_op__=staticmethod(BoolExpr.__invert__)
    __backend_fun__=lambda: None
    def __init__(self, p1):
        self.__depth__=p1.__depth__ + 1
        self.children=(p1, )
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, force_expr=False):
        #!!p = p. Double Negation.
        if isinstance(p1, BoolNotExpr):
            return p1.children[0]
        
        return BoolNotExpr(p1)

class BoolImplExpr(BoolExpr):
    __slots__=()
    __function__="=>"
    __python_op__=staticmethod(BoolExpr.__rshift__)
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2):
        return BoolImplExpr(p1, p2)

class EqExpr(BoolExpr):
    __slots__=()
    __function__="="
    __commutative__=True
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.__sort__ == p2.__sort__
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__
    
    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p EQ p <=> True. Idempotence.
        if p1.__hash__() == p2.__hash__():
            return True if not force_expr else TrueExpr
        return EqExpr(p1, p2)

class DistinctExpr(BoolExpr):
    __slots__=()
    __function__="distinct"
    __commutative__=True
    __backend_fun__=lambda: None
    def __init__(self, p1, p2):
        assert p1.__sort__ == p2.__sort__
        self.__depth__=max(p1.__depth__, p2.__depth__) + 1
        self.children=(p1, p2)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(p1, p2, force_expr=False):
        #p NE p <=> False. Idempotence.
        if p1.__hash__() == p2.__hash__():
            return False if not force_expr else FalseExpr
        return DistinctExpr(p1, p2)

class BoolIteExpr(BoolExpr):
    __slots__=()
    __function__="ite"
    __backend_fun__=lambda: None
    def __init__(self, _if, _then, _else):
        assert isinstance(_if, BoolExpr)
        assert _then.__sort__ == _else.__sort__
        self.__depth__=max(_if.__depth__, _then.__depth__, _else.__depth__) + 1
        self.children=(_if, _then, _else)
        self.__backend__=self.__backend_fun__
        self.__hash__=self.__hash_fun__

    @staticmethod
    def construct(_if, _then, _else):
        return BoolIteExpr(_if, _then, _else)

LRUCACHE_SIZE=1000

#Remeber to initialize the LRU cache with the "most cache-able" expression for extra speed
EqExpr.construct = staticmethod(LruCache(EqExpr.construct, maxsize = LRUCACHE_SIZE)) 
BoolExprCache = EqExpr.construct

for cls in (BoolNotExpr, BoolAndExpr, BoolOrExpr, BoolXorExpr, BoolImplExpr, \
            BoolVarExpr, DistinctExpr, BoolIteExpr):
    cls.construct = staticmethod(LruCache(cls.construct, shared_parameters=BoolExprCache.shared_parameters)) 
