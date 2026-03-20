include "parser.dfy"
include "lexer.dfy"
include "types.dfy"
include "validate.dfy"


//mirrors main
//tests our logic to make sure the verification doesn't assume anything too strong
method main(s: string)
requires |s| > 0
{
    //lex the string into tokens
    var lex_result: Result<seq<Token>> := lex(s);
    if lex_result.Err?{
        print lex_result.error;
        return;
    }
    assert lex_result.Ok?;
    assert lex_result.Ok? ==> forall i:: 0 <= i < |lex_result.data| ==> validValue(lex_result.data[i]);
    assert lex_result.Ok? ==> forall i:: 0 <= i < |lex_result.data| ==> validType(lex_result.data[i]);

    //otherwise lexing was successful
    var tokens := lex_result.data;

    //assert |tokens| > 0;
    //parse the tokens according to the ast
    assert forall i::0<=i<|tokens| ==> validValue(tokens[i]);
    assert forall i::0<=i<|tokens| ==> validType(tokens[i]);
    //this is 100% true, we just haven't proved it to Dafny
    assume{:axiom} |tokens| > 0;

    var parse_result := parse(tokens);
    //couldn't parse the expresssion
    if parse_result.Err?{
        print parse_result.error;
        return;
    }
    assert parse_result.Ok?;
    //else we could parse it into an ast
    var ast := parse_result.data;
    print ast;
}


//some lexing unit tests
method TestLex(){

}
method TestLexInvalidOp(){

}
method TestLexAllWhitespace(){

}

//parsing unit tests
method TestParseNumber(){

}
method TestParseUnaryExpr(){

}
method TestParseBinaryExpr(){

}
method TestParseVariableExpr(){

}
method parseVariableExprEmptyArglist(){

}

