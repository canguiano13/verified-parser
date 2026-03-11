import sys
#import VerifiedParser TODO import this once done with the verified program

#print output
def pretty_print(tokens):
    indent = "\t"
    factor = 4

    #TODO figure out logic for pretty printing
    #tokens is a nested tree structure with a root expression and one or more subexpressions



#print an error message and exit immediately
def error(message):
    sys.stderr.write(f"Error: {message}\n")
    sys.stderr.write(f"Example usage: python3 main.py \"(+ 1 2 (-4 3))\"\n")
    sys.exit(1)


def main():
    #throw an error if the user doesn't provide the expression
    if len(sys.argv) <= 1:
        error("Please provide an expression to parse")

    #get the expression to parse from the user
    expr = sys.argv[-1]
    print(expr)

    #TODO fill in parsing from dafny here
    #lex the tokens from the user's expression
    #tokens = lex(expr)

    #parse the tokens derived into an AST
    #ast = parse(tokens)


    ast = [] #TODO remove this, we will call parse to bind ast 

    pretty_print(ast)


if __name__ == "__main__":
    main()
