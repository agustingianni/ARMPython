"""
TODO:
    a INEQ b AND b INEQ c => a INEQ c (transitivity)
 
    make a constraint switcher to negate constraints one by one (related to the previous check).
    (add a switch limiter for loops)

    constraint subsumption (from SAGE docs)
        Syntactic check for implication, take strongest constraint
        Moreover, using a cheap syntactic check, constraint subsumption eliminates
        constraints logically implied by other constraints injected at
        the same program branch (mostly likely due to successive
        iterations of an input-dependent loop).

"""

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
    trivial=False #used for optimizations that allow us to bypass the solver

    #Overload all set methods to support hash caching
    def add(self, elem):
        set.add(self, elem)
        self.dirty=True

    def clear(self):
        self.solverObj=None
        self.result=None
        self.dirty=True
        self.hashcode=None
        self.trivial=False
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
        """
        Detects trivial cases where the system is either SAT or UNSAT.
        The solverObj is left in an inconsistent state for those cases and
        model() returns True instead of a real model (because the system is VALID).
        """

        s = self.solverObj = z3.SolverFor(solverFor)
        self.trivial = False

        if disjunction:
            tmp = FalseExpr
            for constrain in self:
                tmp |= constrain
                
                #check for the existence of p | ~p
                if isinstance(constrain, BoolNotExpr) and constrain.children[0] in self:
                    self.trivial=True
                    self.result=z3.sat
                    return self.result
            
            s.add(tmp)
        else:
            for constrain in self:
                #check for the existence of p & ~p
                if isinstance(constrain, BoolNotExpr) and constrain.children[0] in self:
                    self.trivial=True
                    self.result=z3.unsat
                    return self.result

                s.add(constrain)
        
        self.result = s.check()
        return self.result
    
    def model(self):
        """
        Return a model for variables that make the system be SAT.
        Also returns True if the system is VALID and None if UNSAT.
        """
        if self.result == z3.sat:
            if self.trivial:
                return True
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
        
        keyword: related constraint optimization
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
    
    #check trivial
    bset = BooleanExpressionSet()
    bset.add(w1 > 0)
    bset.add(~(w1 > 0))
    
    print bset
    print bset.solve()
    
    print bset.solve(True)
    print bset.model()
    
if __name__=="__main__":
    test()
