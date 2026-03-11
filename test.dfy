//TODO might be good to separate the testing from the lexing and parsing
include "parser.dfy"


//unit tests for tagging
//TODO we can probably remove this because the lexer will include this logic
method testTag()
requires true
ensures true
{
    //TODO implement
    assume{:axiom} false;

}

//unit tests for lexing
method testLex()
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
    //create empty list of tokens with only EOF token
    var tokens1: seq<Token> := [];
    var eof_token: Token := Pair(TokenType.EOF, "");
    //add to tokens
    //tokens1 := tokens1 + eof_token;
    //var result1: Result := parse(tokens1);
    //make sure that our parser returns an error
    //assert result1.error == "unexpected end of file";

    //TODO implement
    assume{:axiom} (false);
assume{:axiom} false;

}
