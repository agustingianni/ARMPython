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

    def __repr__(self):
        return "<%s>" % self

    def __str__(self):
        children_repr=[str(x) for x in self.children]
        return "%s(%s)" % (self.__function__, ", ".join(children_repr))

    def export(self, fmt="smtlib2"):
        pass

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
