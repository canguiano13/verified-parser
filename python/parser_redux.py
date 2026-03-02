import sys

"""
Context free grammar that more or less describes the subset of the language we're parsing

<P>             ::= <expr>
<expr>          ::= <unary-op> | <binary-op> | <variable-op> | <num>
<expr-list>     ::= <expr> <expr-list> | ε
<unary-op>      ::= (<unary> <expr>)
<binary-op>     ::= (<binary> <expr> <expr>)
<variable-op>   ::= (<variable> <expr> <expr> <expr-list>)
<unary>         ::= abs | sqrt | ceil | -
<binary>        ::= modulo | expt
<variable>      ::= min | max | + | * | - | /
<num>           ::= -<digits> | <digits> 
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
VALID_OPS = {"abs", "sqrt", "ceil", "mod", "expt", "+", "-", "*", "/", "min", "max"}

#built-in identifiers
keywords = {
        "abs": "UNARY_OP", 
        "sqrt" : "UNARY_OP",
        "ceil" : "UNARY_OP",
        "modulo": "BINARY_OP",
        "expt" : "BINARY_OP",
        "min" : "VARIABLE_OP",
        "max" : "VARIABLE_OP",
}

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
    elif c == '+':
        tokens = addToken("PLUS", "+", tokens)
    elif c == '-':
        #TODO there's an issue with negative numbers. 
        #this will definitely be a challenge we talk about in our presentation/report
        #we'll assume the parser can detect when we're talking about a minus
        tokens = addToken("MINUS", "-", tokens)
    elif c == '*':
        tokens = addToken("STAR", "*", tokens)
    elif c == '/':
        tokens = addToken("SLASH", "/", tokens)
    else:
        #check if its a number
        if (isDigit(c)):
            #if so, the start is current-1 because we just consumed a number
            #lex the entirey of the number
            tokens, current = lex_number(s, current-1, current, tokens)
        #otherwise check if its a keyword
        elif (isAlpha(c)):
            #if so, again we just consumed a character, so should start at current-1
            #then lex the entirety of the identifier
            tokens, current = lex_identifier(s, current-1, current, tokens)
        else:
            error(f"unexpected character \'{c}\'")
    return tokens, current


#consume a number literal
def lex_number(s: str, start: int, current: int, tokens: list):
    #don't need to store the character, it'll be picked up later
    #might have to just use a sequence when we convert to dafny and 
    #gradually add characters to a result string one at a time?
    #add digits to number
    while(isDigit(peek(s, current))):
          _, current = advance(s, current) 

    #check to see if it's a fractional number and add any remaining digits
    if peek(s, current) == '.' and isDigit(peekNext(s, current)):
        #if it is consume the dot
        #TODO might want to use advance here in the Dafny version to make sure it's safe!
        current += 1
        #then add the fractional part
        while(isDigit(peek(s, current))):
              _, current = advance(s, current) 

    #add the token
    #return the token and keep track of the index
    return (addToken("NUMBER", s[start:current], tokens), current)

def lex_identifier(s: str, start: int, current: int, tokens: list):
    while(isAlphaNumeric(peek(s, current))):
        _, current = advance(s, current)

    #check that identifier is in list of valid identifiers
    identifier_val = s[start:current]
    #not a valid operation
    if identifier_val not in keywords:
        error(f"unexpected identifier \"{identifier_val}\"")
    return addToken(keywords.get(identifier_val), identifier_val, tokens), current

#------------------------------------------PARSING----------------------------------------------
"""
Context free grammar that more or less describes the subset of the language we're parsing

<P>             ::= <expr>
<expr>          ::= <unary-op> | <binary-op> | <variable-op> | <num>
<expr-list>     ::= <expr> <expr-list> | ε
<unary-op>      ::= (<unary> <expr>)
<binary-op>     ::= (<binary> <expr> <expr>)
<variable-op>   ::= (<variable> <expr> <expr> <expr-list>)
<unary>         ::= abs | sqrt | ceil 
<binary>        ::= modulo | expt
<variable>      ::= min | max | + | * | - | /
<num>           ::= -<digits> | <digits> 
"""
#some token selectors
def token_t(token: tuple):
    return token[0]
def token_v(token: tuple):
    return token[1]

#create an AST based on a set of tokens and the language grammar
def parse(tokens):
    #start parsing all of the tokens
    #all programs start as an expression
    ast, current = expr(tokens, 0)

    #make sure that all tokens were parsed
    #we should see an EOF
    #current should be == len(tokens)-1 
    (last_token_type, _) = tokens[current]
    if last_token_type != "EOF":
        error(f"unexpected token at end of expression \"{last_token_type}\"")
    return ast

def expr(tokens: list, current: int):
    #expression is either a number or some kind of operation
    #check the first token to see if it starts with '(' or a number
    token_type, token_val = tokens[current]

    #if it's EOF, then we're reached the end of expression unexpectedly, throw an error
    if token_type == "EOF":
        error("unexpected EOF")
    #next, check the type. if it's a number, parse the full number
    elif token_type == "NUMBER":
        #consume the number
        return number(tokens, current)
    elif token_type == "LEFT_PAREN":
        #consume the left parenthesis
        current += 1 
        #check the type of the expression and parse accordingly
        return op(tokens, current)
    else:
        error(f"unrecognized token \"{token_val}\"")

def number(tokens: list, current: int):
    #numbers are essentially already parsed for us during lexing, so just
    return tokens[current], current+1

def op(tokens:list, current: int):
    #ops can be unary, binary, or variable length
    token_type, token_val = tokens[current]
    #consume operator
    current += 1

    #minus needs to be handled separately because it could either be a unary or variable op
    if token_type == "MINUS":
        return minus(token_type, tokens, current)
    #otherwise handle the operation based on its type
    elif token_type == "UNARY_OP":
        return unary_op(token_val, tokens, current) 
    elif token_type == "BINARY_OP":
        return binary_op(token_val, tokens, current)
    elif token_type == "VARIABLE_OP" or token_type in {"PLUS", "STAR", "SLASH"}:
        return variable_op(token_val, tokens, current)
    else:
        error(f"unexpected operation \"{token_val}\"")
    

#always consist of a single argument
def unary_op(op: str, tokens: list, current: int):
    arg, current = expr(tokens, current)
    #consume right parenthensis
    current += 1
    return ("UNARY_OP", op, arg), current
def binary_op(op: str, tokens: list, current: int):
    arg1, current = expr(tokens, current)
    arg2, current = expr(tokens, current)
    #consume right parenthsis
    current += 1
    return ("BINARY_OP", op, arg1, arg2), current
def variable_op(op: str, tokens: list, current: int):
    arg1, current = expr(tokens, current)
    arg2, current = expr(tokens, current)
    
    arglist = [arg1, arg2]
    while token_t(tokens[current]) != "RIGHT_PAREN":
        nextArg, current = expr(tokens, current)
        arglist.append(nextArg)
        
    #consume right parenthesis
    current += 1
    return ("VARIABLE_OP", op, arglist), current

#minus is either a unary op for negative numbers or variable op for subtraction
def minus(op: str, tokens: list, current: int):
    #parse the first argument
    arg1, current = expr(tokens, current)

    #peek ahead by a token to see if it's a right paren or another number
    #if the next token is right parent and current token is a number, we have a negative number operation
    if token_t(tokens[current]) == "RIGHT_PAREN":
        #consume right parenthesis
        current += 1
        #update the type and return the value
        return ("UNARY_OP", "-", arg1), current
    #otherwise we have 2+ numbers
    arg2, current = expr(tokens, current)
    args = [arg1, arg2]
    while token_t(tokens[current]) != "RIGHT_PAREN":
        nextArg, current = expr(tokens, current)
        args.append(nextArg)
    #consume right parenthesis
    current += 1
    return ("VARIABLE_OP", "-", args), current

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

    expression = sys.argv[-1]
    print(expression)

    tokens = lex(expression)
    '''
    print(tokens)
    for token in tokens:
        print(token)
    '''
    ast = parse(tokens)
    print(ast)

    '''
    for nest in ast:
        print(nest)
    '''


if __name__ == "__main__":
    main()




