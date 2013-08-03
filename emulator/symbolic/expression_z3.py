from emulator.symbolic.base_expr import Expr
from emulator.symbolic.boolean_expr import *
from emulator.symbolic.bitvector_expr import *
from emulator.symbolic.memory import DeferredMemRead, AbstractMemoryMap
import inspect
from itertools import starmap
import z3, z3core, z3types, z3printer

def unwrap_args(args, kw):
    newargs=[x.__backend__ if isinstance(x, Expr) else x for x in args]
    if isinstance(kw, dict): 
        newkw=dict(starmap(lambda k,v: (k, v if not isinstance(v, Expr) else v.__backend__), kw.iteritems()))
    else:
        newkw=kw
    return (newargs, newkw)

def decorate_fun(f):
    def wrapper(*args, **kwargs):
        #print "fun", type(args), type(kwargs), f
        (args, kwargs) = unwrap_args(args, kwargs)
        return f(*args, **kwargs)
    return wrapper
    
def decorate_method(f):
    '''
    http://wiki.python.org/moin/PythonDecoratorLibrary#Class_method_decorator_using_instance
    '''

    class descript(object):
        def __init__(self, f):
            self.f = f

        def __get__(self, instance, klass):
            if instance is None:
                return self.make_unbound(klass)
            return self.make_bound(instance)
        
        def make_unbound(self, klass):
            def wrapper(*args, **kwargs):
                #print "unbound method", type(args), type(kwargs), self.f, klass
                (args, kwargs) = unwrap_args(args, kwargs)
                return self.f(*args, **kwargs)
            return wrapper

        def make_bound(self, instance):
            def wrapper(*args, **kwargs):
                #print "bound method", type(args), type(kwargs), self.f, type(instance)
                (args, kwargs) = unwrap_args(args, kwargs)
                return self.f(instance, *args, **kwargs)

            setattr(instance, self.f.__name__, wrapper)
            return wrapper

    return descript(f)

def wrap_module(mod):
    typ=dir(z3types)
    cor=dir(z3core)
    printer=set(dir(z3printer)) - set("obj_to_string")
    for fname, fun in inspect.getmembers(mod, lambda x: inspect.isfunction(x)):
        if fname in typ or fname in cor or fname in printer:
            continue

        if fname[0] != "_" and fname[0:2] != "Z3" and fname != "main_ctx":
            #print "decorating function " + fname
            setattr(mod, fname, decorate_fun(fun))
        
    for name, obj in inspect.getmembers(mod, lambda x: inspect.isclass(x)):
        if name in typ or name in cor or name in printer:
            continue

        if name in ("Context", ):
            continue

        for fname, fun in inspect.getmembers(obj, lambda x: inspect.ismethod(x)):
            #print "decorating method " + fname
            setattr(obj, fname, decorate_method(fun))
        setattr(mod, name, obj)

wrap_module(z3)

def wrapper(*a):
    #arguments wrap
    (ctor, z3_ctor) = a
    def wrapper_func(self, *args):
        ctor(self, *args)
        if None == self.__backend__:
            if isinstance(z3_ctor, tuple):
                newargs = z3_ctor[0](self) #args wrapper
                self.__backend__ = z3_ctor[1](*newargs)
            else:
                self.__backend__ = z3_ctor(*args)
    
    return wrapper_func

def var_wrapper(expr):
    return (expr.name, expr.size)

def boolvar_wrapper(expr):
    return (expr.name, )

def extract_wrapper(expr):
    return (expr.end, expr.start, expr.children[0])

def abstractmemory_wrapper(expr):
    return ("mem", z3.BitVecSort(expr.address_size), z3.BitVecSort(8))

def deferredread_wrapper(expr):
    return (expr.memmap.__backend__, expr.children[0])

def z3_executeMemCommit(self, gen, changes):
    for addr, val in changes:
        if not isinstance(addr, BvExpr):
            addr = z3.BitVecVal(addr, self.address_size)
        if not isinstance(val, BvExpr):
            val = z3.BitVecVal(val, 8)

        self.__backend__ = z3.Store(self.__backend__, addr, val)

AbstractMemoryMap.executeMemCommit = z3_executeMemCommit
    
mapping = {
   BvConstExpr:   z3.BitVecVal,
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
   BoolIteExpr:  z3.If,
   AbstractMemoryMap: (abstractmemory_wrapper, z3.Array),
   DeferredMemRead: (deferredread_wrapper, z3.Select),
}

for expr, z3func in mapping.iteritems():
    expr.__init__ = wrapper(expr.__init__, z3func)

Expr.z3_expr = lambda self: self.__backend__
Expr.solve = lambda self, **kwargs: z3.solve(self, **kwargs)  
Expr.prove = lambda self, **kwargs: z3.prove(self, **kwargs)
BvExpr.z3_bv2int = lambda self: z3.BV2Int(self)
TrueExpr.__backend__ = z3.BoolVal(True)
FalseExpr.__backend__ = z3.BoolVal(False)

def bool_toExpr(self):
    if z3.is_true(self):
        return TrueExpr
    elif z3.is_false(self):
        return FalseExpr
    else:
        return BoolVarExpr.construct(str(self))

class Z3ArrayExpr(Expr):
    children = () 
    __depth__ = 1
    def __init__(self, backend):
        self.size = 8
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__ = "(Array (_ BitVec %d) (_ BitVec 8))" % backend.domain().size()
        self.__backend__ = backend
        self.__function__ = backend.decl()
    
    def __str__(self):
        return "array"
    
class Z3BvExpr(BvExpr):
    def __init__(self, backend):
        self.size = backend.size()
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__ = "(_ BitVec %d)" % self.size
        self.__backend__ = backend
        tmp = backend.sexpr()[1:].split(" ")[0]
        if tmp == "let":
            tmp = backend.decl()
        self.__function__ = tmp
        self.children = tuple([ x.toExpr() for x in backend.children() ])
        self.__depth__ = self._get_depth()
    
    def _get_depth(self):
        if not len(self.children):
            return 1
        return max([x._get_depth() if hasattr(x, "_get_depth") else x.__depth__ for x in self.children])

def bv_toExpr(self):
    if z3.is_bv_value(self):
        return BvConstExpr.construct(self.as_long(), self.size())
    elif z3.is_const(self):
        #constant expression
        return BvVarExpr.construct(self.size(), str(self))
    else:
        return Z3BvExpr(self)
        

z3.BoolRef.toExpr = bool_toExpr
z3.BitVecRef.toExpr = bv_toExpr
z3.ArrayRef.toExpr = lambda self: Z3ArrayExpr(self)