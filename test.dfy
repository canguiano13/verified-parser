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
    var lex_result := lex(s);
    if lex_result.Err?{
        print lex_result.error;
    }
    //otherwise lexing was successful
    var tokens := lex_result.data;

    //parse the tokens according to the ast
    var parse_result := parse(tokens);
    if parse_result.Err?{
        print parse_result.error;
    }
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

