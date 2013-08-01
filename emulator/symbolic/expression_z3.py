from emulator.symbolic.base_expr import Expr
from emulator.symbolic.boolean_expr import *
from emulator.symbolic.bitvector_expr import *
import z3

def wrapper(*a):
    #arguments wrap
    (ctor, z3_ctor) = a
    def wrapper_func(self, *args):
        ctor(self, *args)
        if None == self.__backend__:
            newargs=[]
            for arg in args:
                if isinstance(arg, Expr):
                    newargs.append(arg.__backend__)
                else:
                    newargs.append(arg)
            if isinstance(z3_ctor, tuple):
                newargs = z3_ctor[0](self) #args wrapper
                self.__backend__ = z3_ctor[1](*newargs)
            else:
                self.__backend__ = z3_ctor(*newargs)
    
    return wrapper_func

def var_wrapper(expr):
    return (expr.name, expr.size)

def boolvar_wrapper(expr):
    return (expr.name, )

def extract_wrapper(expr):
    return (expr.end, expr.start, expr.children[0].__backend__)

mapping = {BvConstExpr:   z3.BitVecVal,
           BvVarExpr:     (var_wrapper, z3.BitVec), 
           BvConcatExpr:  z3.Concat,
           BvExtractExpr: (extract_wrapper, z3.Extract),
           BvNotExpr:     z3.BitVecRef.__invert__,
           BvNegExpr:     z3.BitVecRef.__neg__,
           BvAndExpr:     z3.BitVecRef.__and__,
           BvOrExpr:      z3.BitVecRef.__or__,
           BvXorExpr:     z3.BitVecRef.__xor__,
           BvAddExpr:     z3.BitVecRef.__add__,
           BvSubExpr:     z3.BitVecRef.__sub__,
           BvMulExpr:     z3.BitVecRef.__mul__,
           BvUDivExpr:    z3.UDiv,
           BvURemExpr:    z3.URem,
           BvShlExpr:     z3.BitVecRef.__lshift__,
           BvShrExpr:     z3.BitVecRef.__rshift__,
           BvUgtExpr:    z3.UGT,
           BvUgeExpr:    z3.UGE,
           BvUltExpr:    z3.ULT,
           BvUleExpr:    z3.ULE,
           BvUgtExpr:    z3.UGT,
           BvIteExpr:    z3.If,
           BoolNotExpr:  z3.Not,
           BoolAndExpr:  z3.And,
           BoolOrExpr:   z3.Or,
           BoolXorExpr:  z3.Xor,
           BoolImplExpr: z3.Implies,
           BoolVarExpr:  (boolvar_wrapper, z3.Bool),
           EqExpr:       z3.ExprRef.__eq__, 
           DistinctExpr: z3.ExprRef.__ne__,
           BoolIteExpr:  z3.If 
           }

for expr, z3func in mapping.iteritems():
    expr.__init__ = wrapper(expr.__init__, z3func)

Expr.z3_expr = lambda self: self.__backend__
Expr.z3_simplify = lambda self: z3.simplify(self.__backend__)
Expr.solve = lambda self, **kwargs: z3.solve(self.__backend__, **kwargs)  
Expr.prove = lambda self, **kwargs: z3.prove(self.__backend__, **kwargs)
BvExpr.bv2int = lambda self: z3.BV2Int(self.__backend)

class ExprSolver(z3.Solver):
    def __unwrap_args(self, args):
        newargs=[]
        for arg in args:
            if isinstance(arg, Expr):
                newargs.append(arg.__backend__)
            else:
                newargs.append(arg)
        return tuple(newargs)

    def assert_exprs(self, *args):
        return z3.Solver.assert_exprs(self, *self.__unwrap_args(args))

    def assert_and_track(self, *args):
        return z3.Solver.assert_and_track(self, *self.__unwrap_args(args))

    def check(self, *args):
        return z3.Solver.check(self, *self.__unwrap_args(args))

def ExprSolverFor(logic, ctx=None):
    s=z3.SolverFor(logic, ctx)
    return ExprSolver(s.solver, s.ctx)
