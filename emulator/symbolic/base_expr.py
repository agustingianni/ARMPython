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

  process extracts on partial and/or/xor masks or shifts

- There's different levels of optimizations that might apply to an expression.
- It should never be expected to receive the naive operation application from an expression
- It should not be expected to receive an Expression as a result of an operation.
  (unless there's a specific option in the function that forces the response to be an expression)

Optimization rules:
- the pythonic methods might receive native data types (not derived from Expr) and the optimizations must
  cope with that.
- All parameters of the operation classes must be Expr derived instances
- The operation class constructor don't apply any kind of optimization, all work is done in the construct()
  function.
- All construct() functions have a force_expr argument that forces the answer to be a Expr derived instance.
  
'''

class Expr:
    __has_value__=False
    __commutative__=False
    __hashcode__=None
    __backend__=None

    def __repr__(self):
        return "<%s>" % self

    def __str__(self):
        children_repr=[str(x) for x in self.children]
        return "%s(%s)" % (self.__function__, ", ".join(children_repr))
    
    def sort(self):
        return self.__sort__
    
    def export_smtlib2(self, subexpr_mindepth=5, subexpr_max=50):
        """
        The 3-tuple return has dependencies in the order it's return.
        """

        self.init_export()
        self.calculate_subexpr_cache(subexpr_mindepth, subexpr_max)
        expr = self.export()
        cache = self.format_subexpr_cache()
        variables = self.format_variables()
        
        return (variables, cache, expr)

    def format_variables(self):
        ret=[]
        for k,v in self.export_variables.iteritems():
            ret.append("(declare-fun %s () %s)" % (k, v.__sort__))
        
        return "\n".join(ret)
    
    def format_subexpr_cache(self):
        ret=[]
        for h in self.used_subexpr:
            (v, idx) = self.subexpr_cache[h]
            v.export_variables = self.export_variables
            v.subexpr_cache = self.subexpr_cache
            v.used_subexpr = self.used_subexpr
            ret.append("(define-fun subexpr_%d () %s %s)" % (idx, v.__sort__, v.export(False)))
        
        return "\n".join(ret)
    
    def calculate_subexpr_cache(self, subexpr_mindepth, subexpr_max):
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
            if isinstance(v, Expr) and v.__depth__ >= subexpr_mindepth:
                self.subexpr_cache[h] = (v, index)
                index+=1
            
            if index == subexpr_max:
                break
        
        bool_count=index
        bv_count=0
        for (h, _) in BvExprCache.uses.most_common():
            v=_bitvec[h]
            if isinstance(v, Expr) and v.__depth__ >= subexpr_mindepth:
                self.subexpr_cache[h] = (v, index)
                index+=1
                bv_count+=1
            
            if bv_count == subexpr_max:
                break
        
        return (bool_count, bv_count)
    
    def init_export(self):
        self.export_variables={}
        self.subexpr_cache={}
        self.used_subexpr=set()

    def export(self, with_cache=True):
        """
        Export an expr to smtlib2 format.
        """
        
        #save variables
        if self.__depth__ == 1 and not self.__has_value__:
            if not self.name in self.export_variables:
                self.export_variables[self.name] = self
            else:
                assert hash(self) == hash(self.export_variables[self.name])

        if with_cache and self.__hash__() in self.subexpr_cache:
            self.used_subexpr.add(self.__hash__())
            return "subexpr_%d" % self.subexpr_cache[self.__hash__()][1]

        if hasattr(self, "__export__"):
            return self.__export__()

        if len(self.children):
            children_exp=[]
            for x in self.children:
                #transfer state to children
                x.export_variables = self.export_variables
                x.subexpr_cache = self.subexpr_cache
                x.used_subexpr = self.used_subexpr
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
