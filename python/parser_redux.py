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
        "LEFT_PAREN", "RIGHT_PAREN", "DOT", "MINUS", "PLUS", "SLASH", "STAR",
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

#------------------------------------------LEXING----------------------------------------
#main lexing function that will give us our list of tagged tokens
def lex(s: str):
   return scanTokens(s, 0, 0)

#simple helper function that tells us when we've consumed all the characters
def isAtEnd(s, current):
    return current >= len(s)

#another useful function
def isDigit(c):
    return ord(c) >= ord('0') and ord(c) <= ord('9')
def isAlpha(c):
    return (ord(c) >= ord('a') and ord(c) <= ord('z')) or \
           (ord(c) >= ord('A') and ord(c) <= ord('Z')) or \
           (c == '_')
def isAlphaNumeric(c):
    return isAlpha(c) or isDigit(c)

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

    #add EOF after all tokens are scanned
    #this will make parsing a little cleaner
    addToken("EOF", "", tokens)
    return tokens

#add a token with both a type and value to the growing list of existing tokens
def addToken(token_type: str, token_val:str, tokens: list):
    tokens.append((token_type, token_val))
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
        tokens = addToken("LEFT_PAREN", "(", tokens)
    elif c == ')':
        tokens = addToken("RIGHT_PAREN", ")", tokens)
    elif c == '.':
        tokens = addToken("DOT", ".", tokens)
    elif c == '-':
        tokens = addToken("MINUS", "-", tokens)
    elif c == '+':
        tokens = addToken("PLUS", "+", tokens)
    elif c == '*':
        tokens = addToken("STAR", "*", tokens)
    elif c == '/':
        tokens = addToken("SLASH", "/", tokens)
    else:
        #check if its a number
        if (isDigit(c)):
            #if so, the start is current - 1 because we just consumed a number
            tokens, current = lex_number(s, current-1, current, tokens)
        #otherwise check if its a keyword
        elif (isAlpha(c)):
            #if so, again we just consumed a character
            tokens, current = identifier(s, current-1, current, tokens)
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
        return False, current
    return (True, current + 1)

#lookahead but do not consume the next character
def peek(s: str, current: int):
    if isAtEnd(s, current):
        return "\0"
    return s[current]

#lookahead but an extra character
def peekNext(s: str, current: int):
    if (current+1 >= len(s)):
        return '\0'
    return s[current + 1]

#consume a number literal
def lex_number(s: str, start: int, current: int, tokens: list):
    #don't need to store the character, it'll be picked up later
    #might have to just use a sequence when we convert to dafny and 
    #gradually add characters to a result string one at a time?
    while(isDigit(peek(s, current))):
          _, current = advance(s, current) 

    #check to see if it's a fractional number
    if peek(s, current) == '.' and isDigit(peekNext(s, current)):
        #if it is consume the dot
        current += 1
        #then add the fractional part
        while(isDigit(peek(s, current))):
              _, current = advance(s, current) 

    #add the token
    #return the token and keep track of the index
    return (addToken("NUMBER", s[start:current], tokens), current)

def identifier(s: str, start: int, current: int, tokens: list):
    while(isAlphaNumeric(peek(s, current))):
        _, current = advance(s, current)

    #check that identifier is in list of valid identifiers
    identifier_val = s[start:current]
    if identifier_val not in VALID_OPS:
        error(f"unexpected identifier \"{identifier_val}\"")
    return addTokenNonempty("IDENTIFIER", identifier_val, tokens), current

#------------------------------------------PARSING----------------------------------------------
#create an AST based on a set of tokens and the language grammar
def parse(tokens: list):
    ast, look_ahead = parse_expr(tokens, 0)
    return ast

#error handling..
def error(reason):
    print(f"Error in expression: {reason}")
    sys.exit(1)

#main is acting like run() for now...
def main():
    #user doesn't provide the expression
    if len(sys.argv) <= 1:
        print("Error: please provide an expression to parse.\ne.g. \"python3 parser.py \'(+ 1 2 3)\'\"")
        sys.exit(1)

    expr = sys.argv[-1]
    print(expr)

    tokens = lex(expr)
    print(tokens)
    for token in tokens:
        print(token)

    #ast = parse(tokens)


if __name__ == "__main__":
    main()




