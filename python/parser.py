import os
import sys

#AST structure?
class Tree:
    pass

#defines the valid tokens in the language
def tokens():
    valid_tokens = {"(", ")", "abs", "sqrt", "mod", "expt", "sqrt", "+", "-", "*", "/", "min", "max"}
    #later add the list operations
    return valid_tokens

#parse the input text stream into tokens
def lex(sentence: str):
    pass

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


if __name__ == "__main__":
    main()
