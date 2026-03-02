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

//unit tests for tagging
method testTag()
requires true
ensures true
{
    //TODO implement
    assume{:axiom} false;

}

//-------------------------------PARSING--------------------------------

//transform a set of tokens into an AST
//returns Failure if expression is invalid
    //e.g. parentheses don't match
    //e.g. wrong number of operands for a given operation
    //etc
method parse(tokens: seq<Token>) returns (ast: Expr)
requires true
ensures true
{
    //TODO implement
    assume{:axiom} false;

}

//unit tests for parsing
method testParse()
requires true
ensures true
{
    //TODO implement
    assume(false);
assume{:axiom} false;

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