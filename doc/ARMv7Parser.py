"""
Python parser for the ARM Architecture Reference Manual (ARMv7-A and ARMv7-R edition)
pseudocode.
"""
from pyparsing import *
from collections import namedtuple
import string

# Enable optimizations.
ParserElement.enablePackrat()

# Define basic tokens.
LPAR, RPAR, LBRACK, RBRACK, LBRACE, RBRACE, SEMI, COMMA, COLON, EQUALS, LANGLE, RANGLE = map(Suppress, "()[]{};,:=<>")
QUOTE = Suppress("'") ^ Suppress('"')

# Define basic keywords.
IF = Keyword("if")
THEN = Keyword("then")
ELSE = Keyword("else")
ELSIF = Keyword("elsif")
WHILE = Keyword("while")
DO = Keyword("do")
REPEAT = Keyword("repeat")
UNTIL = Keyword("until")
FOR = Keyword("for")
TO = Keyword("to")
CASE = Keyword("case")
OF = Keyword("of")
WHEN = Keyword("when")
OTHERWISE = Keyword("otherwise")
RETURN = Keyword("return")
BIT = Keyword("bit")
BITSTRING = Keyword("bitstring")
INTEGER = Keyword("integer")
BOOLEAN = Keyword("boolean")
REAL = Keyword("real")
ENUMERATION = Keyword("enumeration")
LIST = Keyword("list")
ARRAY = Keyword("array")

# Commonly used constants.
TRUE = Keyword("TRUE")
FALSE = Keyword("FALSE")
UNKNOWN = Keyword("UNKNOWN")
UNDEFINED = Keyword("UNDEFINED")
UNPREDICTABLE = Keyword("UNPREDICTABLE")
SEE = Keyword("SEE")
IMPLEMENTATION_DEFINED = Keyword("IMPLEMENTATION_DEFINED")
SUBARCHITECTURE_DEFINED = Keyword("SUBARCHITECTURE_DEFINED")

# Define the types of each of the translatable units.
BooleanValue = namedtuple("BooleanValue", ["value"])
Identifier = namedtuple("Identifier", ["name"])
NumberValue = namedtuple("NumberValue", ["value"])
List = namedtuple("List", ["values"])
Enumeration = namedtuple("Enumeration", ["values"])
UnaryExpression = namedtuple("UnaryExpression", ["type", "expr"])
BinaryExpression = namedtuple("BinaryExpression", ["type", "left_expr", "right_expr"])
ProcedureCall = namedtuple("ProcedureCall", ["name", "arguments"])
RepeatUntil = namedtuple("RepeatUntil", ["statements", "condition"])
While = namedtuple("While", ["condition", "statements"])
For = namedtuple("For", ["from_", "to", "statements"])
If = namedtuple("If", ["condition", "statements"])
BitExtraction = namedtuple("BitExtraction", ["identifier", "range"])
MaskedBinary = namedtuple("MaskedBinary", ["value"])
Case = namedtuple("Case", ["cases"])
Ignore = namedtuple("Ignore", [])

def decode_case(x):
    return x

def decode_repeat_until(x):
    return RepeatUntil(x[1], x[3])

def decode_for(x):
    return For(x[1], x[3], x[4])

def decode_while(x):
    return While(x[1], x[3])

def decode_unary(x):
    op_name = {"!" : "negate", "-" : "minus", "~" : "invert", "+" : "plus"}
    op = op_name[x[0]]
    return UnaryExpression(op, x[1])

def decode_binary(x):
    op_name = {"+" : "add", "-" : "sub", "/" : "div", "*" : "mul", \
        "<<" : "lshift", ">>" : "rshift", "DIV" : "div", "MOD" : "mod", \
        "^" : "xor", "||" : "or", "&&" : "and", "==" : "eq", "!=" : "ne", \
        ">" : "gt", "<" : "lt", ">=" : "gte", "<=" : "lte", "IN" : "in", \
        "=" : "assign", "EOR" : "xor", ":" : "concatenation"}
    return BinaryExpression(op_name[x[1]], x[0], x[2])

def decode_if(x):
    return If(x[1], x[3])

def decode_bit_extract(x):
    return BitExtraction(x[0], list(x[1]))

def decode_masked_base2(x):
    return MaskedBinary(x[0])

boolean_value = (TRUE ^ FALSE).setParseAction(lambda x: BooleanValue(x == "TRUE"))
identifier = Word(alphas + "_", alphanums + "_.").setParseAction(lambda x: Identifier(x[0]))

# Unary operators.
unary_operator = oneOf("! - ~ +")

# Binary Operators. 
integer_operators = oneOf("+ - / * << >> DIV MOD ^")
boolean_operator = oneOf("|| && == != > < >= <= EOR")
in_operator = Literal("IN")
bitstring_operator = Literal(":")
assignment_operator = Literal("=")
binary_operator = (integer_operators ^ boolean_operator ^ bitstring_operator)

# Use the already defined C multiline comment and C++ inline comments.
comment = cppStyleComment

# Define an integer for base 2, 10 and 16 and make sure it is 32 bits long.
base_2_masked = (QUOTE + Word("01x") + QUOTE).setParseAction(decode_masked_base2)
base2_integer = (Literal("'") + Word("01") + Literal("'")).setParseAction(lambda s, l, t: NumberValue(int(t[1], 2) & 0xffffffff))
base10_integer = Word(initChars=string.digits).setParseAction(lambda s, l, t: NumberValue(int(t[0]) & 0xffffffff))
base16_integer = Regex("0x[a-fA-F0-9]+").setParseAction(lambda s, l, t: NumberValue(int(t[0], 16) & 0xffffffff))

number = (base2_integer ^ base10_integer ^ base16_integer ^ base_2_masked)

# Enumeration ::= {var0, 1, 2} | "01x"
enum_elements = delimitedList(identifier ^ number)
enum_expr = Group(LBRACE + enum_elements + RBRACE).setParseAction(lambda x: Enumeration(x[0][:])) ^ base_2_masked

ignore_value = Literal("-").setParseAction(lambda x: Ignore())

# Atoms are the most basic elements of expressions.
expr = Forward()
parenthized_expr = (LPAR + expr + RPAR)
atom = identifier ^ number ^ enum_expr ^ boolean_value ^ parenthized_expr ^ ignore_value

# Define a procedure call and its allowed arguments.
procedure_argument = number ^ identifier ^ expr
procedure_arguments = delimitedList(procedure_argument)
procedure_call_expr = Group(identifier + LPAR + Optional(procedure_arguments) + RPAR).setParseAction(lambda x: ProcedureCall(x[0][0],x[0][1:]))

# We define a primary to be either an atom or a procedure call.
primary = (atom ^ procedure_call_expr)

# Define a bit extraction expression.
bitextraction_expr = (primary + LANGLE + Group(primary + Optional(COLON + primary)) + RANGLE).setParseAction(decode_bit_extract)

# Define a unary expression.
unary_expr = Forward()
unary_expr <<= primary ^ (unary_operator + unary_expr).setParseAction(decode_unary) ^ bitextraction_expr

# Define a binary expression.
binary_expr = Forward()
binary_expr <<= unary_expr ^ ((unary_expr + binary_operator + binary_expr) ^ (unary_expr + in_operator + enum_expr)).setParseAction(decode_binary)

# Define a boolean expression.
boolean_expr = Forward()
boolean_expr <<= binary_expr ^ (binary_expr + boolean_operator + boolean_expr).setParseAction(decode_binary)

# List expression.
list_elements = delimitedList(boolean_expr)
list_expr = Forward()
list_expr <<= boolean_expr ^ Group(LPAR + list_elements + RPAR).setParseAction(lambda x: List(x[0][:]))

# Generic expression, comprising all the combinations of the preceeding definitions.
expr <<= list_expr

# Forward declaration of a generic statement.
statement = Forward()
statement_list = OneOrMore(statement)

# Simple statements.
undefined_statement = UNDEFINED
unpredictable_statement = UNPREDICTABLE
see_allowed = string.letters + string.digits + " -()/\","
see_statement = Group(SEE + Word(see_allowed + " "))
implementation_defined_statement = Group(IMPLEMENTATION_DEFINED + Word(see_allowed))
subarchitecture_defined_statement = Group(SUBARCHITECTURE_DEFINED + Word(see_allowed))
return_statement = Group(RETURN ^ (RETURN + expr))
procedure_call_statement = procedure_call_expr

# Assignment statement.
assignment_statement = (expr + assignment_operator + expr).setParseAction(decode_binary)

# Define the whole if (...) then ... [elsif (...) then ...] [else ...]
# if_statement = \
#    IF + Optional(LPAR) + expr + Optional(RPAR) + THEN + statement_list + \
#    ZeroOrMore(ELSIF + Optional(LPAR) + expr + Optional(RPAR) + THEN + statement_list) + \
#    Optional(ELSE + statement_list)
#
# Define a simplified if statement. TODO: In the future we ma want to extend it.
if_statement = (IF +  expr + THEN + statement_list).setParseAction(decode_if)

# Define a case statement.
case_list = Group(OneOrMore(WHEN + expr + statement_list))
otherwise_case = Group(OTHERWISE + statement_list)
case_statement = (CASE + expr + OF + case_list + Optional(otherwise_case)).setParseAction(decode_case)

# Repeat until statement.
repeat_until_statement = (REPEAT + statement_list + UNTIL + expr ).setParseAction(decode_repeat_until)

# While statement.
while_statement = (WHILE + expr + DO + statement_list).setParseAction(decode_while)

# For statement.
for_statement = (FOR + assignment_statement + TO + expr + statement_list).setParseAction(decode_for)

# Collect all statements. We have two kinds, the ones that end with a semicolon and if, for and other statements that do not.
statement <<= Group(((undefined_statement ^ unpredictable_statement ^ see_statement ^ \
    implementation_defined_statement ^ subarchitecture_defined_statement ^ return_statement ^ \
    procedure_call_statement ^ assignment_statement) + SEMI) ^ \
    if_statement ^ repeat_until_statement ^ while_statement ^ for_statement ^ case_statement)

# Define a basic program.
program = statement_list

from doc.ARMv7DecodingSpec import instructions

def main():
    #print case_statement.parseString("case val of\nwhen 1\npepe();\nwhen 1\npepe();\notherwise\npepe();")
    #print program.parseString("case val of\nwhen 1\npepe();\nwhen 1\npepe();\notherwise\npepe();")
    #print program.parseString("case val of\nwhen '1'\npepe();\nwhen '1'\npepe();\notherwise\npepe();")

    p = """
case type of
    when '1'
        regs = 1;
    when '2'
        regs = 2;
    otherwise
        regs = 3;
    """
    # TODO: 
    # if (DN:Rdn) == '1101' || Rm == '1101' then SEE ADD (SP plus register);
    # if wback && registers<n> == '1' then UNPREDICTABLE;
    # if Rn == '1111' then SEE LDRB literal;
    
    p = """(-, shift_n) = DecodeImmShift('10', imm5);"""
    
    for s in program.parseString(p):
        print s
    return 

    i = -1
    for ins in instructions:
        i += 1
        
        if i < 678:
            continue
        
        print i 
        try:
            program.parseString(ins["decoder"])
        except ParseException, e:
            print "FAIL: ", ins["name"]
            print ins["decoder"]
            print e
            break    
    
    return

    print program.parseString("registers = P:M:'0':register_list;")
    print program.parseString("if !Consistent(Rm) then UNPREDICTABLE;")
    print program.parseString("(shift_t, shift_n) = (SRType_LSL, 0);")
    print program.parseString("registers = P:M:'0':register_list;")
    print program.parseString("registers = P:M:'0':register_list;")
    print program.parseString("registers = P:M:'0':register_list;")
    print program.parseString("registers = P:M:'0':register_list;")

    return

if __name__ == '__main__':        
    main() 
    