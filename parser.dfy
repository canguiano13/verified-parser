include "test.dfy"
include "lexer.dfy"

/* more or less the grammar we're parsing

<P>             ::= <expr>
<expr>          ::= <unary-op> | <binary-op> | <variable-op> | <num>
<expr-list>     ::= <expr> <expr-list> | ε
<unary-op>      ::= (<unary> <expr>)
<binary-op>     ::= (<binary> <expr> <expr>)
<variable-op>   ::= (<variable> <expr> <expr> <expr-list>)
<unary>         ::= abs | sqrt | ceil | -
<binary>        ::= modulo | expt
<variable>      ::= min | max | + | * | - | /
<num>           ::= (- <digits>) | <digits>
<digits>        ::= <digit> | <digit> <digits>
<digit>         ::= 1 | 2 | .. | 9
*/

//define the possible token types as an enum
datatype TokenType = LEFT_PAREN | RIGHT_PAREN | DOT | MINS | PLUS | STAR | SLASH 
                     | UNARY_OP | BINARY_OP | VARIABLE_OP | NUMBER | EOF

//define the possible operations that have identifiers longer than a single character
datatype BuiltInOp = ABS | SQRT | CEIL | MODULO | EXPT | MIN | MAX

//tokens are specific type of tuples
datatype Token = Pair(token_type:TokenType, token_value:string)

//nodes of the AST come from the grammar
datatype Expr = Number(value: string)
              | UnaryOp(op: string, arg: Expr)
              | BinaryOp(op:string, arg1: Expr, arg2: Expr)
              | VariableOp(op: string, argList: seq<Expr>)

//result datatype will either allow us to store a value
//or it will produce an error/failure
//has to be generic so we can store Expr or Token
datatype Result<T> = Ok(data: T) | Err(error: string)



//------------------------LEXING-------------------------------
//transform user input into a set of tokens
method lex(s: string) //returns (tokens: seq<string>)
requires true
ensures true
{
    //TODO implement
    assume(false);

    assume(false);
assume{:axiom} false;

}


//add type tags to all of the tokens before passing to parser
//TODO probably remove this, i don't actually think we need this.
method tag(tokens: seq<string>) returns (tagged_tokens: seq<Token>)
requires true
ensures true
{
    //TODO implement
    assume{:axiom} false;
}

//-------------------------------PARSING--------------------------------
//transform a set of tokens into an AST
//returns Err if expression is invalid 
//otherwise returns Ok containing the AST root
method parse(tokens: seq<Token>) returns (result: Result<Expr>)
//preconditions
//list of tokens should be nonempty
requires |tokens| > 0
//postconditions
//TODO add ensures...
//TODO the index for the list should be at the end of the list, indicating all tokens were parsed
//TODO should guarantee that the last token is EOF and was parsed
//TODO should guarantee that all of the tokens were consumed into the tree
{
    
    //parse starting at first token
    var ast: Result<Expr>, current_idx: int := expr(tokens, 0);

    //last token should be the EOF token
    //TODO fix these lines once parsing is done
    //assert 0 <= current_idx < |tokens|;
    //assert current_idx == |tokens| - 1;

    //make sure that after parsing ends, the last token is EOF
    assume{:axiom} 0 <= current_idx < |tokens|;
    assume{:axiom} current_idx == |tokens| - 1;
    if tokens[current_idx].token_type == TokenType.EOF{
        return Err("unexpected end of file");
    }

    current_idx := current_idx + 1;
    assert current_idx == |tokens|;
    return ast;
}

//parse an expression
method expr(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
//TODO add ensures
{
    //start with the first token, should be 
    var first_token: Token := tokens[0];
    var token_type := first_token.token_type;
    var token_val := first_token.token_value;

    return Err("TODO implement function"), current_idx + 1;

    //parse a number token
    if token_type == TokenType.NUMBER{
        //TODO implement number() function
        return Err("TODO implement number function"), current_idx + 1;
    }
    //parse some operation
    else if token_type == TokenType.LEFT_PAREN{
        return Err("TODO implement op function"), current_idx + 1;

    }
    //unrecognized token
    else{
        return Err("unrecognized expression"), current_idx + 1;
    }
 
}

//TODO parse a single number token with token at index current_idx
method number(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
//ensure that we consumed at least one token
ensures end_idx > current_idx
{
    return Err("TODO implement function"), current_idx + 1;
}

//TODO dispatch to one of the operation-parsing functions
method op(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
//ensure that we consumed at least one token
ensures end_idx > current_idx
//TODO add ensures
{
    return Err("TODO implement function"), current_idx + 1;

}

//TODO parse a single unary operation starting at token with index current_idx
method unaryOp(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
{
    return Err("TODO implement function"), current_idx + 1;
}
//TODO parse a single binary operation starting at token with index current_idx
method binaryOp(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
{
    return Err("TODO implement function"), current_idx + 1;
}
//TODO parse a single variable-param operation starting at token with index current_idx
method variableOp(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
{
    return Err("TODO implement function"), current_idx + 1;
}

//TODO parse an operation using the minus operator
//either has to be subtraction or negation
method minus(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
//TODO add ensures
{
    return Err("TODO implement function"), current_idx + 1;
}




method main()
requires true
ensures true
{
    //so..funny story. dafny doesn't actually support taking in input or producing simple output.
    //from the Dafny documentation FAQ
    /*
        Question
        How do I read a file as a string?
    
        Answer
        You can’t in pure Dafny. Not yet. Such a capability will eventually be part of a standard IO library.

        What you can do is to write such a function in another language, say Java, and then use it in Dafny by extern declarations.
    */
    //maybe we can do this and then add some python interface that extends the functionality like he was talking about in lecture
    //I would imagine that we can create some python file like main.py, then import the needed function
    //from the transpiled parser.py file.
    assume(false);
}