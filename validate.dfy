include "types.dfy"

predicate validtype(token: Token){
    token.token_type==LEFT_PAREN ||
    token.token_type==RIGHT_PAREN ||
    token.token_type==MINUS ||
    token.token_type==PLUS ||
    token.token_type==STAR ||
    token.token_type==SLASH ||
    token.token_type==NUMBER ||
    token.token_type==UNARY_OP ||
    token.token_type==BINARY_OP ||
    token.token_type==VARIABLE_OP ||
    token.token_type==SPACE
}
//true if a token's value is a whitespace character
predicate ValidWhiteSpace(tok: Token){
    tok.token_value==" " || tok.token_value=="\n" || tok.token_value=="\t"
}
//true if a single character is a whitespace character
predicate isWhiteSpace(ch: char){
    ch==' ' || ch=='\n' || ch=='\t'
}
//only one dot in the string representing the number..avoids malformed numbers like 3.1.4
predicate oneDot(token_value: string){
    true
}
//true if a token representing a Number has a valid value
predicate ValidNumber(tok: Token){
    forall i::0<=i<|tok.token_value| ==> 
        (((tok.token_value[i] as int >= 48 && tok.token_value[i] as int <= 57) || tok.token_value[i]=='.'))
   
}
//true if a token's value is any valid operation in the language
predicate ValidOp(operationValue: string){
    operationValue == "+" || operationValue == "-" ||
    operationValue == "*" || operationValue == "/" ||
    operationValue == "abs" || operationValue == "sqrt" || operationValue == "ceil" ||
    operationValue == "modulo" || operationValue == "expt" ||
    operationValue == "min" || operationValue == "max"
}
//true if a token's value is a valid unary operation
predicate ValidUnary(token_value: string){
    token_value=="abs" || token_value=="sqrt" || token_value=="ceil"
}
//true if a token's value is a valid binary operation
predicate ValidBinary(token_value: string){
    token_value=="modulo" || token_value=="expt"
}
//true if a token's value is a valid variable-argument operation
predicate ValidVariable(token_value: string){
    token_value == "+" || token_value == "-" || 
    token_value == "*" || token_value == "/" || 
    token_value == "min" || token_value == "max"
}
//true if a token's value is a valid multi-length identifer for an operation
predicate ValidString(str: seq<char>){
    str=="abs" ||
    str=="sqrt" ||
    str=="ceil" ||
    str=="modulo" ||
    str=="expt" ||
    str=="min" ||
    str=="max"

}

//true if a token representing a valid unary operation has the correct type
predicate validUnaryTok(tok: Token)
{
    tok.token_type == UNARY_OP && ValidUnary(tok.token_value)
}
//true if a token representing a valid binray operation has the correct type
predicate validBinaryTok(tok: Token)
{
    tok.token_type == BINARY_OP && ValidBinary(tok.token_value)
}
//true if the token representing a valid variable-argument operation has the correct type
predicate validVariableTok(tok: Token)
{
    (tok.token_type == TokenType.VARIABLE_OP ||
    tok.token_type == TokenType.PLUS ||
    tok.token_type == TokenType.STAR ||
    tok.token_type == TokenType.SLASH ||
    tok.token_type == TokenType.MINUS) &&
    ValidVariable(tok.token_value)
}

//true if a token's type is a valid variable operation type
predicate validVariableType(token_type: TokenType){
    token_type == MINUS ||
    token_type == PLUS ||
    token_type == STAR ||
    token_type == SLASH ||
    token_type == VARIABLE_OP
}

//true if a token has a valid token type
predicate validType(tok: Token){
    tok.token_type==LEFT_PAREN ||
    tok.token_type==RIGHT_PAREN ||
    tok.token_type==MINUS ||
    tok.token_type==PLUS ||
    tok.token_type==STAR ||
    tok.token_type==SLASH ||
    tok.token_type==NUMBER ||
    tok.token_type==UNARY_OP ||
    tok.token_type==BINARY_OP ||
    tok.token_type==VARIABLE_OP
}



//true if at token with a valid type has a valid token value
//i.e. it's type implies that it is an appropriate operation for that type
predicate validValue(tok: Token){
    (tok.token_type==UNARY_OP ==> ValidUnary(tok.token_value)) &&
    (tok.token_type==BINARY_OP ==> ValidBinary(tok.token_value)) &&
    (tok.token_type==VARIABLE_OP ==> ValidVariable(tok.token_value)) &&
    (tok.token_type==NUMBER ==> ValidNumber(tok)) &&
    (tok.token_type==PLUS ==> tok.token_value=="+") &&
    (tok.token_type==MINUS ==> tok.token_value=="-") &&
    (tok.token_type==STAR ==> tok.token_value=="*") &&
    (tok.token_type==SLASH ==> tok.token_value=="/") &&
    (tok.token_type==LEFT_PAREN ==> tok.token_value=="(") &&
    (tok.token_type==RIGHT_PAREN ==> tok.token_value==")") &&
    (tok.token_type==SPACE ==> ValidWhiteSpace(tok))
}

//true if the token has a valid type, and the value is implied by the type
predicate validToken(tok: Token){
    validType(tok) && validValue(tok)
}


