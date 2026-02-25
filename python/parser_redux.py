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

TOKEN_TYPES = {
        #single char tokens
        "LEFT_PAREN", "RIGHT_PAREN", "DOT", "MINUS", "PLUS", "SLASH", "STAR", "CARET"
        #literals
            #identifier would be something like abs, sqrt, ceil, mod, expt, min, max
            #number could be float or int, we will have to see
        "IDENTIFIER","NUMBER",
        #later we mgiht introduce list keywords
        "EOF"
        }


#can directly just match against +, -, *, /,
#abs, ceil, sqrt, expt, mod, max, min
#TODO maybe add ceil and floor? this requires support for floats
VALID_OPS = {"abs", "sqrt", "ceil", "mod", "expt", "sqrt", "+", "-", "*", "/", "min", "max"}
UNARY_OPS = {"abs", "sqrt", "ceil"}
BINARY_OPS = {"mod", "expt", "-", "/"}
VARIABLE_OPS = {"min", "max", "+", "*"}
VALID_TOKENS = {"(", ")"} #not sure if we even need this
VALID_TYPES = {"LPAREN", "OP", "RPAREN", "NUMBER"}


#main lexing function that will give us our list of tagged tokens
def lex(s: str):
   return scanTokens(s, 0, 0)

#simple helper function that tells us when we've consumed all the characters
def isAtEnd(s, current):
    return current >= len(s)

#takes the input string s and starts generating tokens
#also uses some fields for representing offsets into the string
    #start oints to the first char in the lexeme being scanned
    #current points to the character currently being considered
def scanTokens(s: str, start: int, current: int):
    #list of tokens scanned
    tokens = []

    while not isAtEnd(s, current):
        #scan a single token
        #each turn, we just scan a single token
        tokens, current = scanToken(s, start, current, tokens)
        current += 1

    #add EOF after all tokens are scanned
    #this will make parsing a little cleaner
    addToken("EOF", tokens)
    return tokens

#add a token with both a type and value to the growing list of existing tokens
def addTokenNonempty(token_type: str, token_val: str, tokens:list):
    tokens.append((token_type, token_val))
    return tokens
#add a token with just a type to the growing list of existing tokens
def addToken(token_type: str, tokens: list):
    #empty token with just a value
    tokens.append((token_type, ""))
    return tokens

#scan a single token from the input string
def scanToken(s: str, start: int, current: int, tokens: list):
    #safely advance to get the next token
    c, current = advance(s, current)

    #dispatch on the token to get the right type
    #ignore whitespace
    if c == ' ' or c == '\r' or c == '\t' or c == '\n':
        return tokens, current
    elif c == '(': 
        tokens = addToken("LEFT_PAREN", tokens)
    elif c == ')':
        tokens = addToken("RIGHT_PAREN", tokens)
    elif c == '.':
        tokens = addToken("DOT", tokens)
    elif c == '-':
        tokens = addToken("MINUS", tokens)
    elif c == '+':
        tokens = addToken("PLUS", tokens)
    elif c == '*':
        tokens = addToken("STAR", tokens)
    elif c == '/':
        tokens = addToken("SLASH", tokens)
    else:
        error(f"unexpected character \'{c}\'")

    return tokens, current


#consume the next character in the input and return it
def advance(s: str, current: int):
    return (s[current], current + 1)

#look ahead to see if we can match the current token with a longer, different token
#its like a conditional advance(), where we only consume the current character if its what we're looking for
def match(s: str, current: int, expected: int):
    #reached end of input stream or next character is not the expected character
    if (isAtEnd(s, current) or s[current] != expected):
        return false, current
    return (True, current + 1)

#lookahead but do not consume the next character

def peek(s: str, current: int, expected: int):
    if(isAtEnd(s, current)):
        return "\0"
    return s[current]


#error handling..
def error(reason):
    print(f"Error in expression: {reason}")
    sys.exit(1)

#main is acting like run() for now...
def main():
    #user doesn't provide the expression
    if len(sys.argv) <= 1:
        print("ERR: Please provide an expression to parse.")
        print("e.g. parser.py \"(+ 1 2 3)\"")
        exit(1)

    expr = sys.argv[-1]
    print(expr)

    tokens = lex(expr)
    for token in tokens:
        print(token)

    #ast = parse(tokens)


if __name__ == "__main__":
    main()



#create an AST based on a set of tokens and the language grammar
def parse(tokens: list):
    ast, look_ahead = parse_expr(tokens, 0)
    return ast

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
def lexPrev(s: str):
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
    


