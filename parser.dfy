//need to define a tuple type that hold (token_type, token_value) pairs
datatype Pair = Pair(fst:string, snd:string)

//transform user input into a set of tokens
//replace '(' with ' ( '
//replace ')' with ' ) '
method lex(s: string) //returns (tokens: seq<string>)
requires true
ensures true
{
    //TODO implement
    assume(false);
}

//add type tags to all of the tokens before passing to parser
method tag(tokens: seq<string>) returns (tagged_tokens: seq<Pair>)
requires true
ensures true
{
    assume(false);
}

//transform a set of tokens into an AST
//returns Failure if expression is invalid
    //e.g. parentheses don't match
    //e.g. wrong number of operands for a given operation
    //etc
method parse(tokens: seq<string>) returns (ast: seq<Pair>)
requires true
ensures true
{
    //TODO implement
    assume(false);
}
