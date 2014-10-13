"""
Python parser for the ARM Architecture Reference Manual (ARMv7-A and ARMv7-R edition)
pseudocode.


TODO: 
    - Handle this case -> (shift_t, shift_n) = DecodeImmShift(type, imm5);

"""
from pyparsing import *
from collections import namedtuple
import string

# Avoid treating newlines as whitespaces. " \n\t\r"
ParserElement.setDefaultWhitespaceChars(" \t")
#ParserElement.verbose_stacktrace = True

# Enable optimizations.
ParserElement.enablePackrat()

# Define basic tokens.
LPAR, RPAR, LBRACK, RBRACK, LBRACE, RBRACE, SEMI, COMMA, COLON, EQUALS, LANGLE, RANGLE = map(Suppress, "()[]{};,:=<>")
QUOTE = Suppress("'") ^ Suppress('"')

# New line.
EOL = Suppress(LineEnd())

# Define basic keywords.
IF = Keyword("if")
ENDIF = Keyword("endif")
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
ENDCASE = Keyword("endcase")
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
If = namedtuple("If", ["condition", "if_statements", "then_statements"])
BitExtraction = namedtuple("BitExtraction", ["identifier", "range"])
MaskedBinary = namedtuple("MaskedBinary", ["value"])
Ignore = namedtuple("Ignore", [])
IfExpression = namedtuple("IfExpression", ["condition", "trueValue", "falseValue"])

CaseElement = namedtuple("CaseElement", ["value", "statements"])
Case = namedtuple("Case", ["expr", "cases"])

Undefined = namedtuple("Undefined", [])
Unpredictable = namedtuple("Unpredictable", [])
See = namedtuple("See", ["msg"])
ImplementationDefined = namedtuple("ImplementationDefined", [])
SubArchitectureDefined = namedtuple("SubArchitectureDefined", [])
Return = namedtuple("Return", ["value"])


def decode_case(x):
    case_variable = x[1]
    cases = x[3]

    t = []
    for case in cases:
        value = case[1]
        statements = case[2]
        t.append(CaseElement(value, statements))

    return Case(case_variable, t)

def decode_repeat_until(x):
    return RepeatUntil(x[1], x[3])

def decode_for(x):
    return For(x[1], x[3], x[4])

def decode_while(x):
    return While(x[1], x[3])

def decode_unary(x):
    x = x[0]

    if len(x) != 2:
        raise "Invalid unary operation: %r" % x

    op_name = {"!" : "negate", "-" : "minus", "~" : "invert", "+" : "plus"}
    op = op_name[x[0]]
    return UnaryExpression(op, x[1])

def decode_binary(x):
    op_name = {"+" : "add", "-" : "sub", "/" : "div", "*" : "mul",
        "<<" : "lshift", ">>" : "rshift", "DIV" : "idiv", "MOD" : "imod",
        "^" : "xor", "||" : "or", "&&" : "and", "==" : "eq", "!=" : "ne",
        ">" : "gt", "<" : "lt", ">=" : "gte", "<=" : "lte", "IN" : "in",
        "=" : "assign", "EOR" : "xor", ":" : "concatenation", "AND" : "and", "OR" : "or"}
        
    x = x[0]    
    
    prev_ = x[0]
    for i in range(0, len(x) - 2, 2):
        op, next_ = x[i + 1], x[i + 2]
        prev_ = BinaryExpression(op_name[op], prev_, next_)
        
    return prev_

def decode_if_expression(x):
    return IfExpression(x[1], x[3], x[5])

def decode_if(x):
    return If(x[1], map(lambda x: x[0], list(x[3:])), [])

def decode_if_else(x):
    return If(x[1], list(x[3]), list(x[5]))

def decode_bit_extract(x):
    return BitExtraction(x[0][0], list(x[0][1:]))

def decode_masked_base2(x):
    return MaskedBinary(x[0])

def decode_list(x):
    return List(x[0:])

# Define the boolean values.
boolean = (TRUE ^ FALSE).setParseAction(lambda x: BooleanValue(x == "TRUE"))

# An identifier is a name.
identifier = Word(alphas + "_", alphanums + "_.").setParseAction(lambda x: Identifier(x[0]))

# Unary operators.
unary_operator = oneOf("! - ~ +")

# Bitstring concatenation operator.
bit_concat_operator = Literal(":")

# Product, division, etc.
mul_div_mod_operator = oneOf("* / MOD DIV")

# Binary add and sub.
add_sub_operator = oneOf("+ -")

# Binary shift operators.
shift_operator = oneOf("<< >>")

# Less than, less than or equal, etc.
lt_lte_gt_gte_operator = oneOf("< <= > >=")

# Equal or not equal operators.
eq_neq_operator = oneOf("== !=")

# Bitwise and operator.
bit_and_operator = oneOf("& AND")

# Bitwise eor operator.
bit_eor_operator = oneOf("^ EOR")

# Bitwise or operator.
bit_or_operator = oneOf("| OR")

# Logical and operator.
logical_and_operator = Literal("&&")

# Logical or operator.
logical_or_operator = Literal("||")

# Includes operator
in_operator = Literal("IN")

# Assignment operator.
assignment_operator = Literal("=") 

# Use the already defined C multi-line comment and C++ inline comments.
comment = cppStyleComment

# Define an integer for base 2, 10 and 16 and make sure it is 32 bits long.
base_2_masked = (QUOTE + Word("01x") + QUOTE).setParseAction(decode_masked_base2)
base2_integer = (Literal("'") + Word("01") + Literal("'")).setParseAction(lambda s, l, t: NumberValue(int(t[1], 2) & 0xffffffff))
base10_integer = Word(initChars=string.digits).setParseAction(lambda s, l, t: NumberValue(int(t[0]) & 0xffffffff))
base16_integer = Regex("0x[a-fA-F0-9]+").setParseAction(lambda s, l, t: NumberValue(int(t[0], 16) & 0xffffffff))

# Join all the supported numbers.
number = (base2_integer ^ base10_integer ^ base16_integer ^ base_2_masked)

# Enumeration ::= {var0, 1, 2} | "01x"
enum_elements = delimitedList(identifier ^ number)
enum = Group(LBRACE + enum_elements + RBRACE).setParseAction(lambda x: Enumeration(x[0][:])) ^ base_2_masked

# Ignore '-' value.
ignored = Literal("-").setParseAction(lambda: Ignore())

# Forward declaration of a function call.
procedure_call_expr = Forward()

# Forward declaration of a bit extraction call.
bit_extract_expr = Forward()

# Forward declaration of an if expression.
if_expression = Forward()

# List: (a, b)
list_elements = delimitedList(identifier ^ number ^ boolean ^ ignored ^ procedure_call_expr)
list_expr = (LPAR + list_elements + RPAR).setParseAction(decode_list)

# Atoms are the most basic elements of expressions.
atom = identifier ^ number ^ enum ^ boolean ^ ignored ^ procedure_call_expr ^ bit_extract_expr ^ if_expression ^ list_expr

# Define the order of precedence.
expr = operatorPrecedence(atom, [
    (unary_operator         , 1, opAssoc.RIGHT, decode_unary ),
    (bit_concat_operator    , 2, opAssoc.LEFT , decode_binary),
    (mul_div_mod_operator   , 2, opAssoc.LEFT , decode_binary),
    (add_sub_operator       , 2, opAssoc.LEFT , decode_binary),
    (shift_operator         , 2, opAssoc.LEFT , decode_binary),
    (in_operator            , 2, opAssoc.LEFT , decode_binary),
    (lt_lte_gt_gte_operator , 2, opAssoc.LEFT , decode_binary),
    (eq_neq_operator        , 2, opAssoc.LEFT , decode_binary),
    (bit_and_operator       , 2, opAssoc.LEFT , decode_binary),
    (bit_eor_operator       , 2, opAssoc.LEFT , decode_binary),
    (logical_and_operator   , 2, opAssoc.LEFT , decode_binary),
    (logical_or_operator    , 2, opAssoc.LEFT , decode_binary),
])

# Define a procedure call and its allowed arguments. We do this because things
# break if we get too recursive.
procedure_argument = operatorPrecedence(atom, [
    (unary_operator         , 1, opAssoc.RIGHT, decode_unary ),
    (bit_concat_operator    , 2, opAssoc.LEFT , decode_binary),
    (mul_div_mod_operator   , 2, opAssoc.LEFT , decode_binary),
    (add_sub_operator       , 2, opAssoc.LEFT , decode_binary),
    (shift_operator         , 2, opAssoc.LEFT , decode_binary),
    (bit_and_operator       , 2, opAssoc.LEFT , decode_binary),
    (bit_eor_operator       , 2, opAssoc.LEFT , decode_binary),
])

# Define a bit extraction expression.
bit_extract_expr <<= Group(identifier + LANGLE + (identifier ^ number) + Optional(COLON + (identifier ^ number)) + RANGLE).setParseAction(decode_bit_extract)
    
# Define a procedure call.
procedure_arguments = delimitedList(procedure_argument)
procedure_call_expr <<= Group(identifier + LPAR + Optional(procedure_arguments) + RPAR).setParseAction(lambda x: ProcedureCall(x[0][0], x[0][1:]))

# Define an if expression. 
if_expression <<= (IF + expr + THEN + expr + ELSE + expr).setParseAction(decode_if_expression)

# Forward declaration of a generic statement.
statement = Forward()
statement_list = OneOrMore(statement + Optional(EOL))

# Simple statements.
undefined_statement = UNDEFINED.setParseAction(lambda: Undefined())
unpredictable_statement = UNPREDICTABLE.setParseAction(lambda: Unpredictable())
see_allowed = string.letters + string.digits + " -()/\","
see_statement = Group(SEE + Word(see_allowed + " ")).setParseAction(lambda x: See(x[0][1]))
implementation_defined_statement = Group(IMPLEMENTATION_DEFINED + Word(see_allowed)).setParseAction(lambda: ImplementationDefined())
subarchitecture_defined_statement = Group(SUBARCHITECTURE_DEFINED + Word(see_allowed)).setParseAction(lambda: SubArchitectureDefined())
return_statement = Group(RETURN + Optional(expr)).setParseAction(lambda x: Return(x[0][1]))
procedure_call_statement = procedure_call_expr

# Assignment statement.
assignment_statement = (expr + assignment_operator + expr).setParseAction(lambda x: decode_binary([x]))

# This is used for inline if statements with multiple statements.
inline_statement_list = OneOrMore(statement)

# Parse: if <cond> then st1; st2; st3; ... stn;
single_line_if_statement = (IF + expr + THEN + inline_statement_list).setParseAction(decode_if)

# Parse: if <cond> then <statements> else <statements> endif
multiline_if_statement = (IF + expr + THEN + ZeroOrMore(EOL) + statement_list + ELSE + ZeroOrMore(EOL) + statement_list + ENDIF).setParseAction(decode_if_else)

# Two types of if statements.
if_statement = single_line_if_statement ^ multiline_if_statement

# Define a case statement.
case_list = Group(OneOrMore(Group(WHEN + expr + Optional(EOL) + Group(statement_list))))
otherwise_case = Group(OTHERWISE + Optional(EOL) + Group(statement_list))
case_statement = (CASE + expr + OF + EOL + case_list + Optional(otherwise_case) + ENDCASE).setParseAction(decode_case)

# Repeat until statement.
repeat_until_statement = (REPEAT + statement_list + UNTIL + expr).setParseAction(decode_repeat_until)

# While statement.
while_statement = (WHILE + expr + DO + statement_list).setParseAction(decode_while)

# For statement.
for_statement = (FOR + assignment_statement + TO + expr + statement_list).setParseAction(decode_for)

# Collect all statements. We have two kinds, the ones that end with a semicolon and if, for and other statements that do not.
statement <<= Group(((undefined_statement ^ unpredictable_statement ^ see_statement ^
    implementation_defined_statement ^ subarchitecture_defined_statement ^ return_statement ^
    procedure_call_statement ^ assignment_statement) + SEMI) ^
    if_statement ^ repeat_until_statement ^ while_statement ^ for_statement ^ case_statement) # ^ OneOrMore(EOL)

# Define a basic program.
program = statement_list

def test_specific():
    tests = []

    # PASS
    # tests.append("""if var == 1 then a();""")
    # tests.append("""if var == 1 then a(); b(); c(); d();""")
    # tests.append("""if var == 1 then a();\nb();""")
    # tests.append("""if var == 1 then a(); b();\nc();\nd();""")
    # tests.append("""case var_name of\nwhen 1 a(); b();\nwhen 2 c(); d();\nendcase""")

    for p in tests:
        print "# Testing:"
        print "--------------------------------"
        print "%s" % p
        print "--------------------------------"
        for s in program.parseString(p, parseAll=True):
            for a in s:
                print a
        print

    import sys
    sys.exit()

    return True

def test_all():
    from doc.ARMv7DecodingSpec import instructions

    i = -1
    for ins in instructions:
        i += 1
        
        if not i % 10:
            print "Testing: %.4d - %.4d of %4d" % (i, i + 10, len(instructions))
         
        try:
            program.parseString(ins["decoder"], parseAll=True)
        except ParseException, e:
            print "FAIL: ", ins["name"]
            print ins["decoder"]
            print e
            return False    
    
    return True


def main():
    if True:
        if not test_specific():
            print "Failed individual test cases."

    if True:
        if not test_all():
            print "Failed test of specification."
    
    return 0

if __name__ == '__main__':        
    main() 
