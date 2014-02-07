from emulator.symbolic.base_expr import *
from emulator.symbolic.bitvector_expr import *
from emulator.symbolic.boolean_expr import *
from emulator.symbolic.misc_expr import *
from emulator.symbolic.memory import *
from emulator.symbolic.expression_z3 import *
import itertools

class BooleanExpressionSet(set):
    """
    A BooleanExpressionSet is a Set with extended functions aimed to support
    a set of Boolean Expressions with hashing support for future caching.
    """

    solverObj=None
    result=None
    dirty=True
    hashcode=None

    #Overload all set methods to support hash caching
    def add(self, elem):
        set.add(self, elem)
        self.dirty=True

    def clear(self):
        self.solverObj=None
        self.result=None
        self.dirty=True
        set.clear(self)
    
    def difference(self, other):
        tmp=set.difference(self, other)
        tmp.dirty=True
        return tmp

    def difference_update(self, other):
        set.difference_update(self, other)
        self.dirty=True

    def discard(self, e):
        set.discard(self, e)
        self.dirty=True
    
    def intersection(self, other):
        tmp=set.intersection(self, other)
        tmp.dirty=True
        return tmp

    def intersection_update(self, other):
        set.intersection_update(self, other)
        self.dirty=True
    
    def pop(self):
        tmp = set.pop(self)
        self.dirty=True
        return tmp
    
    def remove(self, e):
        set.remove(self, e)
        self.dirty=True

    def symmetric_difference(self, other):
        tmp=set.symmetric_difference(self, other)
        tmp.dirty=True
        return tmp

    def symmetric_difference_update(self, other):
        set.symmetric_difference_update(self, other)
        self.dirty=True
    
    def union(self, other):
        tmp=set.union(self, other)
        tmp.dirty=True
        return tmp

    def update(self, other):
        set.update(self, other)
        self.dirty=True

    #new methods
    def solve(self, disjunction=False, solverFor="QF_AUFBV"):
        if self.solverObj == None:
            self.solverObj = z3.SolverFor(solverFor)

        s = self.solverObj
        if disjunction:
            tmp = FalseExpr
            for constrain in self:
                tmp |= constrain
            
            s.add(tmp)
        else:
            for constrain in self:
                s.add(constrain)
        
        self.result = s.check()
        return self.result
    
    def model(self):
        if self.result == z3.sat:
            return self.solverObj.model()
        else:
            return None
    
    def __hash__(self):
        if self.dirty:
            tmp=len(self)
            for x in self:
                tmp^=hash(x)
            tmp^=hash(self.result)
            self.hashcode=tmp
            self.dirty=False
        return self.hashcode
    
    def filter(self, v):
        """
        Return a subset of the current set including only the expressions that
        contain variables from the "v" set.
        Always include fully constant expressions.
        """
        
        if isinstance(v, Expr):
            v = (v, )
        
        return BooleanExpressionSet( \
                                    itertools.ifilterfalse( \
                                    lambda x: x.extractVariables() and x.extractVariables().isdisjoint(v), self))

def test():
    bset = BooleanExpressionSet()
    c1=BvVarExpr.construct(8, "c1")
    c2=BvVarExpr.construct(8, "c2")
    c3=BvVarExpr.construct(8, "c3")
    c4=BvVarExpr.construct(8, "c4")
    w1=BvVarExpr.construct(16, "w1")
    d1=BvVarExpr.construct(32, "d1")
    
    cons=BvConstExpr.construct(1, 32)
    cons0=BvConstExpr.construct(0, 32)
    c = BvUgtExpr.construct(cons, cons0)
    tmp=(c1+c2+c3) / 2 == 0

    bset.add(c1 != 0)
    bset.add(tmp)
    bset.add(c)
    print bset
    print hash(bset)
    
    print bset.filter(c3)
    
    print bset.solve()
    print bset.model()
    
    print bset.dirty
    bset.discard(c)
    print bset.dirty
    print bset.copy().dirty
    
if __name__=="__main__":
    test()
