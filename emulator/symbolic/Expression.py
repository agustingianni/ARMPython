'''
Created on Jul 21, 2013

@author: pablo

Bitwise
    AND
    OR
    NOT
    XOR

Shifts
    SHL
    SHR

Arithmetic
    ADD
    SUB
    MUL
    UDIV
    UREM
    NEG

Ordering
    ULT
    ULE
    EQ
    NEQ
    UGT
    UGE
    SLT
    SLE
    SGT
    SGE

Miscellaneous
    CONCAT
    EXTRACT
    ITE
    ZEROEXTEND
    SIGNEXTEND

Constants
    FALSE
    TRUE
    BVCONST

Variables
    BOOL
    BV

Expressions
    BoolExpr
        have pythonic methods for all typical boolean operations
    BVExpr
        have pythonic method for BV operations.
        it never adapts the size of the expression by itself
    
    Once created, the expression should be considered immutable.
    __init__ functions should be avoided as much as possible.
    All type information should be static and part of the class definition.
'''

class Expr:
    def __str__(self):
        pass

class BoolExpr(Expr):
    __type__="boolean"

class BVExpr(Expr):
    __type__="bitvector"
    