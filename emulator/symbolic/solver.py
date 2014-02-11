"""
TODO:
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
    lhs_ineq={}
    rhs_ineq={}

    #Overload all set methods to support hash caching
    def add(self, elem):
        if not isinstance(elem, Expr):
            return

        set.add(self, elem)
        self.dirty=True

    def clear(self):
        self.solverObj=None
        self.result=None
        self.dirty=True
        self.hashcode=None
        self.trivial=False
        self.lhs_ineq={}
        self.rhs_ineq={}
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
    def constraint_transformations_all(self):
        changed=False

        for constraint in self.copy():
            changed |= self.constraint_transformations(constraint)
    
        #recurse until it reaches a fixed point
        if changed:
            self.constraint_transformations_all()
                
        self.dirty=changed
        return changed

    def constraint_transformations(self, constraint):
        """
        This method takes a constraint from the set and lookup the other 
        constraints for relations that might allow to optimize them.
        
        One example could be transitivity over bitvector inequalities.
        """
        
        changed=False

        #p INEQ q AND q INEQ r => p INEQ r
        if isinstance(constraint, BvInequalityExpr):
            lhs=hash((constraint.children[0], constraint.__function__))   #q, >
            rhs=hash((constraint.children[1], constraint.__function__))   #w, >
            
            if rhs in self.lhs_ineq and len(self.lhs_ineq[rhs]):
                #pick one of the options for the right side
                rhs_constraint = self.lhs_ineq[rhs].pop()
                
                #remove the right side constraint from all sets
                rhs_constraint_hash=hash((rhs_constraint.children[1], rhs_constraint.__function__))
                self.rhs_ineq[rhs_constraint_hash].remove(rhs_constraint)
                self.discard(constraint)
                self.discard(rhs_constraint)
                
                self.add( constraint.__class__.construct(constraint.children[0], rhs_constraint.children[1], force_expr=True) )
                changed=True
            elif lhs in self.rhs_ineq and len(self.rhs_ineq[lhs]):
                #pick one of the options for the right side
                lhs_constraint = self.rhs_ineq[lhs].pop()
                
                #remove the right side constraint from all sets
                lhs_constraint_hash=hash((lhs_constraint.children[0], lhs_constraint.__function__))
                self.lhs_ineq[lhs_constraint_hash].remove(lhs_constraint)
                self.discard(constraint)
                self.discard(lhs_constraint)
                
                self.add( constraint.__class__.construct(lhs_constraint.children[0], constraint.children[1], force_expr=True) )
                changed=True
            else:
                if not rhs in self.rhs_ineq:
                    self.rhs_ineq[rhs]=set()
                self.rhs_ineq[rhs].add(constraint)
    
                if not lhs in self.lhs_ineq:
                    self.lhs_ineq[lhs]=set()
                self.lhs_ineq[lhs].add(constraint)
        
        return changed
                        

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
            for constraint in self:
                #check for the existence of a constant boolean expression
                if constraint == FalseExpr:
                    continue
                
                if constraint == TrueExpr:
                    self.trivial=True
                    self.result=z3.sat
                    return self.result
                
                #check for the existence of p | ~p
                if isinstance(constraint, BoolNotExpr) and constraint.children[0] in self:
                    self.trivial=True
                    self.result=z3.sat
                    return self.result
            
                tmp |= constraint

            if constraint == FalseExpr or constraint == TrueExpr:
                self.trivial=True
                self.result=z3.sat if constraint == TrueExpr else z3.unsat
                return self.result

            s.add(tmp)
        else:
            for constraint in self:
                #check for the existence of a constant boolean expression
                if constraint == TrueExpr:
                    continue
                
                if constraint == FalseExpr:
                    self.trivial=True
                    self.result=z3.unsat
                    return self.result

                #check for the existence of p & ~p
                if isinstance(constraint, BoolNotExpr) and constraint.children[0] in self:
                    self.trivial=True
                    self.result=z3.unsat
                    return self.result

                s.add(constraint)
        
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
    bset.add(c1 > c2)
    #bset.add(c2 > c3)
    bset.add(c2 > c1)
    
    print bset
    print bset.constraint_transformations_all()
    print bset
    print bset.solve()
    print bset.trivial
    
    print bset.solve(True)
    print bset.trivial
    print bset.model()
    
if __name__=="__main__":
    test()
