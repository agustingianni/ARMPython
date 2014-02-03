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

- There're different levels of optimizations that might apply to an expression.
- It should never be expected to receive an operator instance for any applied operation (the operation could be optimized away) 
- It should never be expected to receive an Expression as a result of an operation (it could return a Python number for example).
  [unless there's a specific option in the function that forces the response to be an expression]

Optimization rules:
- the pythonic methods might receive native data types (not derived from Expr) and the optimizations must
  cope with that.
- All parameters of the operation classes must be Expr derived instances
- The operation class constructor does NOT apply any kind of optimization, all work is done in the construct()
  function.
- All construct() functions have a force_expr argument that forces the answer to be a Expr derived instance.
  
'''

class Singleton(type):
    _instances = {}
    def __call__(self, *args, **kwargs):
        if self not in self._instances:
            self._instances[self] = super(Singleton, self).__call__(*args, **kwargs)
        return self._instances[self]

class ExportParameters(object):
    """
    Singleton Class/Instance used to accumulate all information needed to export a
    group of constrains to SMTLIB-2.
    
    It includes the function definitions cache to cope with equal subexpressions caching. 
    """
    __metaclass__ = Singleton
    
    def __init__(self):
        self.clear()

    def clear(self):
        self.declares={}
        self.asserts=[]
        self.cache={}
        self.cache_dirty=True
        self.cache_mindepth=5
        self.cache_maxsize=50
    
    def get_decls(self):
        return self.declares.values()
    
    def get_asserts(self):
        return self.asserts
    
    def set_mindepth(self, n):
        self.cache_mindepth = n
    
    def set_maxsize(self, n):
        self.cache_maxsize = n

class Expr(object):
    __slots__=("children", "__depth__", "__hash__", "__backend__", "__solver_ctor__")
    __has_value__=False
    __commutative__=False
    
    def __repr__(self):
        return "<%s>" % self

    def __str__(self):
        children_repr=[str(x) for x in self.children]
        return "%s(%s)" % (self.__function__, ", ".join(children_repr))
    
    def sort(self):
        return self.__sort__
    
    def export_smtlib2(self, subexpr_mindepth=5, subexpr_max=50):
        """
        The 3-tuple return has all declarations first, then the asserts for those decls and
        last, self exported to smtlib2
        """

        ExportParameters().clear()
        ExportParameters().set_mindepth(subexpr_mindepth)
        ExportParameters().set_maxsize(subexpr_max)

        expr = self.export()
        
        return (ExportParameters().get_decls(), ExportParameters().get_asserts(), expr)
    
    def calculate_subexpr_cache(self):
        """
        Separate the <subexpr_max> most common sub-expressions with depth >= mindepth to
        help the solver spot common sub-expressions.
        """

        from emulator.symbolic.boolean_expr import BoolExprCache
        from emulator.symbolic.bitvector_expr import BvExprCache
        
        _bool={hash(v):v for v in BoolExprCache.cache.values()}
        _bitvec={hash(v):v for v in BvExprCache.cache.values()}
        index=0
        for (h, u) in BoolExprCache.uses.most_common():
            #we don't want to cache expressions used just once
            if u == 1:
                break

            v=_bool[h]
            if isinstance(v, Expr) and v.__depth__ >= ExportParameters().cache_mindepth:
                ExportParameters().cache[h] = (v, index)
                index+=1
            
            if index == ExportParameters().cache_maxsize:
                break
        
        bool_count=index
        bv_count=0
        for (h, _) in BvExprCache.uses.most_common():
            v=_bitvec[h]
            if isinstance(v, Expr) and v.__depth__ >= ExportParameters().cache_mindepth:
                ExportParameters().cache[h] = (v, index)
                index+=1
                bv_count+=1
            
            if bv_count == ExportParameters().cache_maxsize:
                break
        
        return (bool_count, bv_count)

    def export(self, with_cache=True):
        """
        Export an expr to smtlib2 format.
        """
        if ExportParameters().cache_dirty:
            self.calculate_subexpr_cache()
            ExportParameters().cache_dirty = False        
        
        #save variables
        if self.__depth__ == 1 and hasattr(self, "name"):
            if not self.name in ExportParameters().declares:
                ExportParameters().declares[self.name] = "(declare-const %s %s)" % (self.name, self.__sort__)
            else:
                assert self.__sort__ in ExportParameters().declares[self.name]

        if with_cache and self.__hash__() in ExportParameters().cache:
            varname = "subexpr_%d" % ExportParameters().cache[self.__hash__()][1]
            if varname not in ExportParameters().declares:
                ExportParameters().declares[varname] = "(declare-const %s %s)" % (varname, self.__sort__)
                ExportParameters().asserts.append("(= %s %s)" % (varname, self.export(False))) 
            return varname

        if hasattr(self, "__export__"):
            return self.__export__()

        if len(self.children):
            children_exp=[]
            for x in self.children:
                children_exp.append(x.export())

            return "(%s %s)" % (self.__function__, " ".join(children_exp))
        else:
            return self.__function__
        

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

    def __hash_fun__(self):
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

        hashcode = hash((self.__sort__, self.__has_value__, tuple(optional), children))
        self.__hash__ = lambda: hashcode
        return hashcode
