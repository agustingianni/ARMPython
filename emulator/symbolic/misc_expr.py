from emulator.symbolic.base_expr import Expr
from emulator.symbolic.bitvector_expr import BvExpr, BvConstExpr, BvIteExpr
from emulator.symbolic.boolean_expr import BoolExpr, TrueExpr, FalseExpr, BoolIteExpr

def IteExpr(_if, _then, _else, op_size=32):
    if isinstance(_if, BoolExpr) and not _if.__has_value__:
        if not isinstance(_then, Expr):
            if isinstance(_then, bool):
                _then=TrueExpr if _then else FalseExpr
            else:
                if isinstance(_else, BvExpr):
                    _then=BvConstExpr.construct(_then, _else.size)
                else:
                    _then=BvConstExpr.construct(_then, op_size)
    
        if not isinstance(_else, Expr):
            if isinstance(_else, bool):
                _else=TrueExpr if _else else FalseExpr
            else:
                if isinstance(_then, BvExpr):
                    _else=BvConstExpr.construct(_else, _then.size)
                else:
                    _else=BvConstExpr.construct(_else, op_size)

        #if _then == _else it doesn't matter what _if says
        (value, secondary, both_values) = _then.getValue(_else)
        if both_values and value == secondary:
            return value

        if isinstance(_then, BoolExpr):
            return BoolIteExpr.construct(_if, _then, _else)
        else:
            return BvIteExpr.construct(_if, _then, _else)
    else:
        if bool(_if):
            return _then.value if isinstance(_then, Expr) and _then.__has_value__ else _then
        else:
            return  _else.value if isinstance(_else, Expr) and _else.__has_value__ else _else
