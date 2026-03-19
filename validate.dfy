include "types.dfy"

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
    tok.token_type==VARIABLE_OP ||
    tok.token_type==EOF
}

//true if at token with a valid type has a valid token value
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
    (tok.token_type==RIGHT_PAREN ==> tok.token_value==")") 
}

//true if the token has a valid type, and the value is implied by the type
predicate validToken(tok: Token){
    validType(tok) && validValue(tok)
}

//true if an expression is well-formed
predicate ValidSubexpression(expr: Expr){
    true
}
//true if 
predicate ValidSubexpressions(exprs: seq<Expr>)
{
    forall i :: 0 <= i < |exprs| ==> ValidSubexpression(exprs[i])
}

