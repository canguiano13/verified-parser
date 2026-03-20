include "types.dfy" 
include "validate.dfy"

/* more or less the grammar we're parsing
<P>             ::= <expr>
<expr>          ::= <unary-op> | <binary-op> | <variable-op> | <number>
<unary-op>      ::= (<unary> <expr>)
<binary-op>     ::= (<binary> <expr> <expr>)
<variable-op>   ::= (<variable> <expr-list>)
<expr-list>     ::= <expr> | <expr> <expr-list>
<unary>         ::= abs | sqrt | ceil
<binary>        ::= modulo | expt
<variable>      ::= min | max | + | * | - | /
<number>        ::= <digits> | <digits> . <digits>
<digits>        ::= <digit> | <digit> <digits>
<digit>         ::= 1 | 2 | .. | 9
*/


//true if an expression is well-formed
//  each expression type should have the correct number of arguments
//  each expression should have a valid operator based on the type of expression it is
//  all subexpressions are well-formed
predicate isWellFormed(expr: Expr){
    //numbers are always be well-formed because of how they are lexed
    (expr.Number? ==> true) &&
    //unary operations should have a valid unary operator and exactly one well-formed subexpression
    (expr.UnaryOp? ==> 
        ValidUnary(expr.op) && isWellFormed(expr.arg)) &&
    //binary operations consist of a valid binary operator and exactly two well-formed subexpressions
    (expr.BinaryOp? ==>
        ValidBinary(expr.op) && isWellFormed(expr.arg1) && isWellFormed(expr.arg2)) &&
    //variable-argument operations consist of a valid variable-argument operator, and at least one well-formed subexpression
    (expr.VariableOp? ==>
        ValidVariable(expr.op) && isWellFormed(expr.arg1) && wellFormedArgList(expr.argList))
}
//true if all subexpressions in an argument list are well-formed
predicate wellFormedArgList(argList: seq<Expr>){
    forall i :: 0 <= i < |argList| ==> isWellFormed(argList[i])
}

//peek ahead by a single token, but do not consume it
//if there are no more tokens, return EOF
method peekToken(tokens: seq<Token>, start_idx: int) returns (result: Token)
requires 0 <= start_idx <= |tokens|
ensures start_idx < |tokens| ==> result == tokens[start_idx]
//if idx is out of bounds, just return EOF
ensures start_idx == |tokens| ==> result.token_type == TokenType.EOF
{
//if there are no more tokens to parse, return EOF
    if start_idx == |tokens|{
        var res := Pair(TokenType.EOF, "EOF");
        return res;
    }

    //otherwise return next token
    result := tokens[start_idx];
}

//some TODOs we might prove next:
//  if tokens has mismatched parens, then must return err
//  if we have n tokens, the depth of the AST should be strictly less than N 
//  if we can parse, this implies the input string is syntactically correct
//  eventually, prove full functional correctness about the parser

//-------------------------------PARSING--------------------------------
//transform a set of tokens into an AST
//returns Err if expression is invalid, otherwise returns Ok containing the AST root
method parse(tokens: seq<Token>) returns (result: Result<Expr>)
//preconditions
//list of tokens should be nonempty
//should be at least one token, otherwise the lexer will reject the expression
requires |tokens| > 0
//all tokens should have a valid type
//this is guaranteed by the lexer
requires forall i :: 0 <= i < |tokens| ==> validToken(tokens[i])
//if the parser can parse the tokens, the resulting tree must be well formed 
//i.e. all tokens have the correct types, and all values should be valid according to their type
ensures result.Ok? ==> isWellFormed(result.data)
{
    //parse starting at first token
    var start_idx := 0;
    var ast: Result<Expr>, end_idx: int := expr(tokens, start_idx);

    //could not parse invalid expression
    if ast.Err?{
        //assert end_idx <= |tokens|;
        return ast;
    }

    //otherwise the expression was successfully parsed
    assert ast.Ok?;

    //should be at the end of the tokens
    if (end_idx != |tokens|){
        return Err("unexpected tokens after expression");
    }

    //now this must be true
    assert end_idx == |tokens|;

    //TODO last thing we need to prove!!
    assert isWellFormed(ast.data);
    return ast;
}

//return an expression representing a number
method number(tokens: seq<Token>, start_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
//our current idx should not be at the end of the list of tokens
requires 0 <= start_idx < |tokens|
//current token should be a number
requires tokens[start_idx].token_type == TokenType.NUMBER
//ensure that we consumed just the number token 
ensures end_idx == start_idx + 1
//no error condition for numbers
ensures result.Ok?
//end index should still be in bounds
ensures result.Ok? ==> 0 <= end_idx <= |tokens|
//if the parser can parse the tokens, the resulting tree must be well formed 
//i.e. all tokens have the correct types, and all values should be valid according to their type
ensures result.Ok? ==> isWellFormed(result.data)
decreases |tokens| - start_idx 
{
    //verify that the current token is a valid number token
    //no other parsing needed than this
    var parsed_num: Expr := Number(tokens[start_idx].token_value);
    return Ok(parsed_num), start_idx + 1;
}

//parse an expression
method expr(tokens: seq<Token>, start_idx: int) returns (result: Result<Expr>, end_idx: int)
//should be at least one token to parse
requires |tokens| > 0
//start_idx must be in bounds
requires 0 <= start_idx < |tokens|
//all tokens should have a valid type
//this is guaranteed by the lexer
requires forall i :: 0 <= i < |tokens| ==> validType(tokens[i])
//all token values should be valid based on the type
requires forall i :: 0 <= i < |tokens| ==> validValue(tokens[i])
//if we can parse the expression, the start_idx pointer must increase
ensures result.Ok? ==> end_idx > start_idx
//if the parser can parse the tokens, the resulting tree must be well formed 
//i.e. all tokens have the correct types, and all values should be valid according to their type
ensures result.Ok? ==> isWellFormed(result.data)
decreases |tokens| - start_idx, 0
{
    //get next token in list
    var next_token: Token := tokens[start_idx];
    var token_type := next_token.token_type;

    //if the expression is a number, parse it
    if token_type == TokenType.NUMBER{
        var parsed_num, end_idx := number(tokens, start_idx);

        //no error condition for numbers
        //asuming the lexer properly lexes them, they are always well-formed and can be parsed
        assert !parsed_num.Err?;

        return parsed_num, end_idx;
    }

    //otherwise token is an expression
    //subexpression should always start with '(', otherwise it's not a valid subexpression, e.g. "(+ 1 + 2 3)"
    //verify that the token we are going to consume is a left paren
    if next_token.token_type != TokenType.LEFT_PAREN{
        return Err("malformed expression. make sure your expression has the appropriate number of arguments and matching parenthesis"), start_idx;
    }
    //consume left parenthesis
    var next_idx := start_idx + 1;

    //check if the subexpression ends after the left parenthesis, e.g. "(+ 1 2 ("
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), start_idx;
    }

    //parse the operation for expression
    result, end_idx := op(tokens, next_idx);
}

//dispatch to one of the operation-parsing functions based on token type
method op(tokens: seq<Token>, start_idx: int) returns (result: Result<Expr>, end_idx: int)
//should be at least one token
requires |tokens| > 0
//start_idx should be in bounds before parsing
requires 0 <= start_idx < |tokens|
//token type should be valid 
requires forall i :: 0 <= i < |tokens| ==> validType(tokens[i])
//all tokens should have a valid value based according to the type
requires forall i :: 0 <= i < |tokens| ==> validValue(tokens[i])
//if we can parse the operation, start_idx must increase
ensures result.Ok? ==> end_idx > start_idx
//if the parser can parse the tokens, the resulting tree must be well formed 
//i.e. all tokens have the correct types, and all values should be valid according to their type
ensures result.Ok? ==> isWellFormed(result.data)
decreases |tokens| - start_idx, 1
{
    //starting token should be an operation 
    //extract the operation type from the current token
    var operation_type: TokenType := tokens[start_idx].token_type;
    var operation_value: string := tokens[start_idx].token_value;

    //consume the operator
    var next_idx := start_idx + 1;

    //if there are no tokens after operator, invalid expression, e.g. "(+ 1 2 (+"
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), start_idx;
    }

    //dispatch to appropriate parsing functon based on the operation type
    if operation_type == TokenType.UNARY_OP{
        result, end_idx := unaryOp(tokens, next_idx, operation_value);
    }
    else if operation_type == TokenType.BINARY_OP{
        result, end_idx := binaryOp(tokens, next_idx, operation_value);
    }
    else if validVariableType(operation_type) {
        result, end_idx := variableOp(tokens, next_idx, operation_value);
    }
    //otherwise not a valid valid operation token
    else{
        result, end_idx := Err("unknown operation '" + operation_value + "'"), start_idx;
    }

}

//parse a single unary operation
method unaryOp(tokens: seq<Token>, start_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
//at least one token to parse
requires |tokens| > 0
//start_idx is in bounds
requires 0 <= start_idx < |tokens|
//token type should be valid 
requires forall i :: 0 <= i < |tokens| ==> validType(tokens[i])
//all tokens should have a valid value based according to the type
requires forall i :: 0 <= i < |tokens| ==> validValue(tokens[i])
//operation should be a valid unary operation
requires ValidUnary(operation)
//if we can parse the unary operation, start_idx must increase
ensures result.Ok? ==> end_idx > start_idx
//if the parser can parse the tokens, the resulting tree must be well formed 
//i.e. all tokens have the correct types, and all values should be valid according to their type
ensures result.Ok? ==> isWellFormed(result.data)
decreases |tokens| - start_idx, 2
{
    //parse the expression after the operator
    var parsed_subexpr, next_idx := expr(tokens, start_idx);
    
    //check if parsing the subexpression fails
    if parsed_subexpr.Err?{
        return parsed_subexpr, next_idx;
    }
    //check if the expression ends without a right_paren, e.g. (+ 1 2 (* 3 4)
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), start_idx;
    }
    //next token should be a right paren
    if tokens[next_idx].token_type != TokenType.RIGHT_PAREN{
        return Err("malformed expression. make sure your expression has the appropriate number of arguments and matching parenthesis"), start_idx;
    }

    //the operation can be parsed
    var parsed_unary_op := Ok(UnaryOp(operation, parsed_subexpr.data));

    //consume right parenthesis
    //return parsed unary op
    result, end_idx := parsed_unary_op, next_idx + 1;
}

//parse a single binary operation starting at token with index current_idx
method binaryOp(tokens: seq<Token>, start_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
//should be at least one token to parse
requires |tokens| > 0
//start_idx should be in bounds
requires 0 <= start_idx < |tokens|
//token type should be valid 
requires forall i :: 0 <= i < |tokens| ==> validType(tokens[i])
//all tokens should have a valid value based according to the type
requires forall i :: 0 <= i < |tokens| ==> validValue(tokens[i])
//operation token should be a valid binary token 
requires ValidBinary(operation)
//if we can parse the binary operation, the index pointer must increase
ensures result.Ok? ==> start_idx < end_idx
//if the parser can parse the tokens, the resulting tree must be well formed 
//i.e. all tokens have the correct types, and all values should be valid according to their type
ensures result.Ok? ==> isWellFormed(result.data)
decreases |tokens| - start_idx, 2
{

    //parse the first subexpressions after the operator
    var parsed_subexpr_1: Result<Expr>, next_idx: int;
    parsed_subexpr_1, next_idx := expr(tokens, start_idx);

    //check if parsing the subexpression fails
    if parsed_subexpr_1.Err?{
        return parsed_subexpr_1, next_idx;
    }
    //check if the first subexpression ends without a right_paren, e.g. "(+ 1 (ceil 4.5" 
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), next_idx;
    }

    //parse the second subexpressions after the operator
    var parsed_subexpr_2: Result<Expr>;
    parsed_subexpr_2, next_idx := expr(tokens, next_idx);

    //check if parsing the second subexpression fails
    if parsed_subexpr_2.Err?{
        return parsed_subexpr_2, next_idx;
    }
    //check if the second subexpression ends without a right_paren, e.g. "(+ 1 2 (* 3 4"
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), next_idx;
    }
    //after parsing both arguments, last token in expression should be a right paren
    if tokens[next_idx].token_type != TokenType.RIGHT_PAREN{
        return Err("malformed expression. make sure your expression has the appropriate number of arguments and matching parenthesis"), next_idx;
    }

    //consume right parenthesis
    next_idx := next_idx + 1;

    //make a binary operation using the current operation and two parsed subexpressions
    var parsed_binary_op := BinaryOp(operation, parsed_subexpr_1.data, parsed_subexpr_2.data);

    //return parsed binary operation
    result, end_idx := Ok(parsed_binary_op), next_idx;
}

//parse a single variable-param operation starting at token with index current_idx
method variableOp(tokens: seq<Token>, start_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
//should be at least one token to parse
requires |tokens| > 0
//start_idx should be valid
requires 0 <= start_idx < |tokens|
//token type should be valid 
requires forall i :: 0 <= i < |tokens| ==> validType(tokens[i])
//all tokens should have a valid value based according to the type
requires forall i :: 0 <= i < |tokens| ==> validValue(tokens[i])
//operation should be a valid binary operation
requires ValidVariable(operation)
//after parsing, all tokens are still valid types
ensures forall i :: 0 <= i < |tokens| ==> validType(tokens[i])
//if the operation can be parsed, start_idx must increase
ensures result.Ok? ==> start_idx < end_idx
//if the parser can parse the tokens, the resulting tree must be well formed 
//i.e. all tokens have the correct types, and all values should be valid according to their type
ensures result.Ok? ==> isWellFormed(result.data)
decreases |tokens| - start_idx, 2
{

    //required to have at least one subexpression after operator
    var parsed_required_subexpression: Result<Expr>, next_idx: int;
    //populate argument list with any remaining arguments
    var subexprList: seq<Expr> := [];

    //parse required expressions after operator
    parsed_required_subexpression, next_idx := expr(tokens, start_idx);
    if parsed_required_subexpression.Err?{
        return parsed_required_subexpression, start_idx;
    }
    //check if the required subexpression ends without a right_paren, e.g. "(+ 1 2 (* 3 4"
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), start_idx;
    }

    assert next_idx < |tokens|;

    //look ahead to next token
    //if it is a RIGHT_PARENT, end of expression. loop terminates
    //otherwise, keep parsing subexpressions and adding to list
    var nextToken: Token := peekToken(tokens, next_idx);

    //until we reach right paren, there are more arguments
    //arguments are numbers or expressions
    while nextToken.token_type != TokenType.RIGHT_PAREN
    //next_idx is always in bounds
    invariant 0 <= next_idx < |tokens|
    invariant wellFormedArgList(subexprList)
    //start_idx pointer always gets closer to the end of the token sequence
    decreases |tokens| - next_idx, 1
    {
        //parse next subexpr
        var next_parsed_subexpr: Result<Expr>;

        //ensure that we are not at the end of the expression prematurely
        if next_idx >= |tokens|{
            return Err("unexpected EOF"), start_idx;
        }

        next_parsed_subexpr, next_idx := expr(tokens, next_idx);

        //ensure that we are not at the end of the expression prematurely
        if next_idx >= |tokens|{
            return Err("unexpected EOF"), start_idx;
        }

        //check if subexpression can't be parsed
        if next_parsed_subexpr.Err?{
            return next_parsed_subexpr, start_idx;
        }

        //add to list of arguments
        subexprList := subexprList + [next_parsed_subexpr.data];

        //move to next token in expression
        nextToken := peekToken(tokens, next_idx);
    }

    var parsed_variable_op := VariableOp(operation, parsed_required_subexpression.data, subexprList);

    //consume right parenthesis
    next_idx := next_idx + 1;

    //just need to prove this now
    assert(isWellFormed(parsed_variable_op));
    assert(wellFormedArgList(parsed_variable_op.argList));

    //return parsed variable-argument operation
    result, end_idx := Ok(parsed_variable_op), next_idx;
}

