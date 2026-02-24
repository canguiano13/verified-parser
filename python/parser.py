import sys

"""
Context free grammar that more or less describes the subset of the language we're parsing

<P>             ::= <expr>
<expr>          ::= <unary-op> | <binary-op> | <variable-op> | <num>
<expr-list>     ::= <expr> <expr-list> | ε
<unary-op>      ::= (<unary> <expr>)
<binary-op>     ::= (<binary> <expr> <expr>)
<variable-op>   ::= (<variable> <expr> <expr> <expr-list>)
<unary>         ::= abs | sqrt | ceil 
<binary>        ::= mod | expt | - | /
<variable>      ::= min | max | + | *
<num>           ::= -<digits> | <digits> 
<digits>        ::= <digit> | <digit> <digit>
<digit>         ::= 0 | 1 | .. | 9
"""

VALID_OPS = {"abs", "sqrt", "ceil", "mod", "expt", "sqrt", "+", "-", "*", "/", "min", "max"}
UNARY_OPS = {"abs", "sqrt", "ceil"}
BINARY_OPS = {"mod", "expt", "-", "/"}
VARIABLE_OPS = {"min", "max", "+", "*"}
VALID_TOKENS = {"(", ")"} #not sure if we even need this
VALID_TYPES = {"LPAREN", "OP", "RPAREN", "NUMBER"}

#create an AST based on a set of tokens and the language grammar
def parse(tokens: list):
    ast, look_ahead = parse_expr(tokens, 0)
    return ast

#parse a single subexpression recursively
def parse_expr(tokens: list, look_ahead: int):
    #should expect that the input is greater than 0
    #get next token
    token_type, token_value = tokens[look_ahead]

    #expression is just a number
    if token_type == "NUMBER":
        look_ahead += 1 
        return (token_value, look_ahead)
    #expression is some subexpression
    elif token_type == "LPAREN":
        #consume "("
        look_ahead += 1

        #get operation
        token_type, token_value = tokens[look_ahead]

        #check that they provided an operation
        if token_type != "OP":
            print("ERROR: NOT A VALID EXPRESSION.")
            print("EXPECTED OPERATOR")
            sys.exit(1)
        
        #parse operation based on remaining number of arguments
        op = token_value
        look_ahead += 1
        if op in UNARY_OPS:
            return parse_unary_op(op, tokens, look_ahead)
        elif op in BINARY_OPS:
            return parse_binary_op(op, tokens, look_ahead)
        elif op in VARIABLE_OPS:
            return parse_variable_op(op, tokens, look_ahead)
        else:
            print("ERROR: ILL-FORMED EXPRESSION")
            print("EXPECTED A NUMBER OR SUBEXPRESSION")
            sys.exit(1)

        #recursively call parse_expr
        #ast = parse_expr(tokens, look_ahead)

def parse_unary_op(op, tokens, look_ahead):
    #guaranteed to have at least one arg
    arg, look_ahead = parse_expr(tokens, look_ahead)
    # consume ')'
    look_ahead += 1
    return (("UNARY_OP", op, arg), look_ahead)

def parse_binary_op(op, tokens, look_ahead):
    #guaranteed to have exactly two arguments
    arg1, look_ahead = parse_expr(tokens, look_ahead)
    arg2, look_ahead = parse_expr(tokens, look_ahead)
    #consume ')'
    look_ahead += 1  
    return (("BINARY_OP", op, arg1, arg2), look_ahead)

def parse_variable_op(op, tokens, look_ahead):
    #guaranteed to have at least two arguments
    arg1, look_ahead = parse_expr(tokens, look_ahead)
    arg2, look_ahead = parse_expr(tokens, look_ahead)
    args = [arg1, arg2]
    #parse remaining args
    while tokens[look_ahead][0] != "RPAREN":
        arg, look_ahead = parse_expr(tokens, look_ahead)
        args.append(arg)
    #consume ')'
    look_ahead += 1
    return (("VARIABLE_OP", op, args), look_ahead)
    
#derive tokens from the input tokens 
#TODO add support for float numbers
def lex(s: str):
    tokens = []
    i = 0
    while i < len(s):
        char = s[i]

        #skip all whitespace
        if char.isspace():
            i += 1
            continue
        #if it's an open parentheses, then we have an expression
        elif char == "(":
            tokens.append(("LPAREN", char))
            i += 1
        #if it's a close parenthesis, we have the end of an expression
        elif char == ")":
            tokens.append(("RPAREN", char))
            i += 1
        #if it's a number, parse the full number
        elif char.isdigit():
            next_token = ""
            #might be a float number
            #TODO add support for floats
            while i < len(s) and s[i].isdigit():
                next_token += s[i]
                i += 1
            tokens.append(("NUMBER", next_token))
        #otherwise it's one of the keywords
        else:
            next_token = ""
            while i < len(s) and not s[i].isspace():
                next_token += s[i]
                i += 1
            if next_token in VALID_OPS:
                tokens.append(("OP", next_token))
            else:
                print(f"ERROR: UNKNOWN TOKEN \"{next_token}\"")
                sys.exit(1)

    return tokens
    


def main():
    #user doesn't provide the expression
    if len(sys.argv) <= 1:
        print("ERR: Please provide an expression to parse.")
        print("e.g. parser.py \"(+ 1 2 3)\"")
        exit(1)

    expr = sys.argv[-1]
    print(expr)

    tokens = lex(expr)
    print(tokens)

    ast = parse(tokens)


if __name__ == "__main__":
    main()
