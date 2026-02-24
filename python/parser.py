import os
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
VALID_TOKENS = {"(", ")"} #not sure if we even need this
VALID_TYPES = {"LPAREN", "OP", "RPAREN", "NUM"}

#create an AST based on a set of tokens and the language grammar
def parse(tokens: list):
    pass
   
#derive tokens from the input tokens 
#TODO add type tags to each token
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

if __name__ == "__main__":
    main()
