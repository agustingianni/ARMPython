from emulator.symbolic.base_expr import Expr
from emulator.symbolic.boolean_expr import *
from emulator.symbolic.bitvector_expr import *
from emulator.symbolic.memory import DeferredMemRead, AbstractMemoryMap
import inspect
import types
from itertools import starmap
import z3, z3core, z3types, z3printer
import traceback

def unwrap_args(args, kw):
#    c=0
#    for x in args:
#        if isinstance(x, Expr):
#            print "arg %d, EXPR: %s" % (c, str(x))
#        else:
#            if type(x) == types.InstanceType: 
#                print "arg %d, Z3: %s" %(c, x.__class__)
#            else:
#                print "arg %d, Z3: %s" %(c, type(x))
#        print traceback.print_stack()
#        c+=1
    newargs=[x.__backend__() if isinstance(x, Expr) else x for x in args]
    if isinstance(kw, dict): 
        newkw=dict(starmap(lambda k,v: (k, v if not isinstance(v, Expr) else v.__backend__()), kw.iteritems()))
    else:
        newkw=kw
    return (newargs, newkw)

def decorate_fun(f):
    def wrapper(*args, **kwargs):
        #print "naked fun", type(args), type(kwargs), f
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
                #print "bound method", type(args), type(kwargs), self.f, instance.__class__
                (args, kwargs) = unwrap_args(args, kwargs)
                return self.f(instance, *args, **kwargs)

            setattr(instance, self.f.__name__, wrapper)
            return wrapper

    return descript(f)

def wrap_module(mod):
    classes_to_wrap = ("ExprRef", "BoolRef", "BitVecRef", "ArrayRef", "SortRef", "BoolSortRef", \
                       "BitVecSortRef", "AstRef", "BitVecNumRef", "ArraySortRef", "ModelRef", \
                       "Solver")
    funs_to_wrap = ("is_ast", "is_expr", "is_app", "is_const", "is_var", "get_var_index", \
                    "is_app_of", "If", "Distinct", "is_bool", "is_true", "is_false", \
                    "is_and", "is_or", "is_not", "is_eq", "is_distinct", "Implies", \
                    "Xor", "Not", "And", "Or", "is_bv", "is_bv_value", "BV2Int", \
                    "Concat", "Extract", "ULE", "ULT", "UGT", "UGE", "UDiv", "URem", \
                    "SRem", "LShR", "RotateLeft", "RotateRight", "SignExt", "ZeroExt", \
                    "RepeatBitVec", "is_array", "is_select", "is_store", "is_const_array", \
                    "is_K", "is_map", "get_map_func", "Update", "Select", "Map", "simplify", \
                    "substitute", "substitute_vars")
    
    if not hasattr(mod, "wrapped_funs"):
        mod.wrapped_funs=set()
    
    for fname in funs_to_wrap:
        if fname in mod.wrapped_funs:
            #print "already wrapped: " + fname
            continue

        fun = getattr(mod, fname)
        
        #print "decorating function " + fname
        args=inspect.getargspec(fun)
        if len(args[0]) == 0 and args[1] == None and args[2] == None and args[3] == None:
            #print "no args functions doesn't need to be wrapped"
            continue
        
        setattr(mod, fname, decorate_fun(fun))
        mod.wrapped_funs.add(fname)
        
    for name in classes_to_wrap:
        obj = getattr(mod, name)
        if not hasattr(obj, "wrapped_funs"):
            obj.wrapped_funs=set()
        for fname, fun in inspect.getmembers(obj, lambda x: inspect.ismethod(x)):
            wholename = name + "." + fname
            if wholename in obj.wrapped_funs:
                #print "already wrapped: " + wholename
                continue

            #print "decorating method " + name + "." + fname
            args=inspect.getargspec(fun)
            if len(args[0]) == 1 and args[1] == None and args[2] == None and args[3] == None:
                #print "no args functions (self only) doesn't need to be wrapped"
                continue

            setattr(obj, fname, decorate_method(fun))
            obj.wrapped_funs.add(wholename)
        setattr(mod, name, obj)

wrap_module(z3)

def bvval_wrapper(expr):
    return (expr.value, expr.size)

def var_wrapper(expr):
    return (expr.name, expr.size)

def boolvar_wrapper(expr):
    return (expr.name, )

def extract_wrapper(expr):
    return (expr.end, expr.start, expr.children[0])

def deferredmemread_backend(self):
    pmem = self.memmap.commited_memory_solver
    target_gen = self.generation
    ret=None
    if target_gen not in pmem:
        #prefetch objects to avoid lookups
        cmem = self.memmap.commited_memory
        addr_size = self.memmap.address_size
        gen = -1
        while target_gen > gen and len(cmem):
            gen, changes = cmem.pop(0)
            ret = pmem[gen - 1]
            for addr, val in changes:
                if not isinstance(addr, BvExpr):
                    addr = z3.BitVecVal(addr, addr_size)
                if not isinstance(val, BvExpr):
                    val = z3.BitVecVal(val, 8)
    
                ret = z3.Store(ret, addr, val)
            pmem[gen] = ret
        
        if gen == -1:
            ret = pmem[target_gen - 1]
    else:
        ret = pmem[target_gen] 
    
    _ret = z3.Select(ret, self.children[0])
    self.__backend__ = lambda: _ret
    return _ret

DeferredMemRead.__backend_fun__ = deferredmemread_backend

class Z3AbstractMemoryMap(AbstractMemoryMap):
    def __init__(self, address_size=32):
        _AbstractMemoryMap.__init__(self, address_size)
        #generation -1 is the "previous" to generation 0
        mem = z3.Array("mem", z3.BitVecSort(address_size), z3.BitVecSort(8))
        self.commited_memory_solver = {-1:mem}

_AbstractMemoryMap = AbstractMemoryMap
AbstractMemoryMap = Z3AbstractMemoryMap
    
mapping = {
   BvConstExpr:   (bvval_wrapper, z3.BitVecVal),
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
}

def get_backend(self):
    if isinstance(self.__solver_ctor__, tuple):
        ret  = self.__solver_ctor__[1](*self.__solver_ctor__[0](self))
    else:
        ret = self.__solver_ctor__(*self.children)
    
    #replaces this function with an empty lambda that returns the pre-computed result
    self.__backend__ = lambda: ret
    return ret

for expr, z3func in mapping.iteritems():
    expr.__solver_ctor__ = staticmethod(z3func)
    expr.__backend_fun__ = get_backend

Expr.z3_expr = lambda self: self.__backend__()
Expr.solve = lambda self, **kwargs: z3.solve(self, **kwargs)  
Expr.prove = lambda self, **kwargs: z3.prove(self, **kwargs)
BvExpr.z3_bv2int = lambda self: z3.BV2Int(self)
TrueExpr.__backend__ = lambda: z3.BoolVal(True)
FalseExpr.__backend__ = lambda: z3.BoolVal(False)

def bool_toExpr(self):
    if z3.is_true(self):
        return TrueExpr
    elif z3.is_false(self):
        return FalseExpr
    else:
        return BoolVarExpr.construct(str(self))

class Z3ArrayExpr(BvExpr):
    __slots__=("__function__")
    children = () 
    __depth__ = 1
    def __init__(self, backend):
        self.size = 8
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__ = "(Array (_ BitVec %d) (_ BitVec 8))" % backend.domain().size()
        self.__backend__ = lambda: backend
        self.__function__ = backend.decl()
    
    def __str__(self):
        return "array"
    
class Z3BvExpr(BvExpr):
    __slots__=("__function__")
    def __init__(self, backend):
        self.size = backend.size()
        self.size_mask = ((2 ** self.size) - 1)
        self.__sort__ = "(_ BitVec %d)" % self.size
        self.__backend__ = lambda: backend
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