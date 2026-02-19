import os
import sys

"""
Context free grammar that describes the subset of the language we're parsing

<P>             ::= <expr>
<expr>          ::= <unary-op> | <binary-op> | <variable-op> | <num>
<expr-list>     ::= <expr> <expr-list> | ε
<unary-op>      ::= (<unary> <expr>)
<binary-op>     ::= (<binary> <expr> <expr>)
<variable-op>   ::= (<variable> <expr> <expr-list>)
<unary>         ::= abs | sqrt 
<binary>        ::= mod | expt | - | /
<variable>      ::= min | max | + | *
<num>   ::= <digit> | <digit> <num>
<digit> ::= 0 | 1 | .. | 9
"""

#AST structure?
#TODO remove if not needed
class Tree:
    pass

#defines the valid tokens in the language
def tokens():
    valid_tokens = {"(", ")", "abs", "sqrt", "mod", "expt", "sqrt", "+", "-", "*", "/", "min", "max"}
    #later add the list operations
    return valid_tokens

#parse the input text stream into tokens
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
        elif char == "(" or char == ")":
            tokens.append(char)
            i += 1
        #if it's a number, parse the full number
        elif char.isdigit():
            next_token = ""
            #might be a float number
            while i < len(s) and (s[i].isdigit() or s[i] == "."):
                next_token += s[i]
                i += 1
            tokens.append(next_token)
        #otherwise it's one of the keywords
        else:
            next_token = ""
            while i < len(s) and not s[i].isspace():
                next_token += s[i]
                i += 1
            tokens.append(next_token)
            i += 1
    return tokens
    

#create an AST based on a set of tokens and the language grammar
def parse(tokens: list):
    pass

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
