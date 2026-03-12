//include "test.dfy" 
//include "lexer.dfy" //TODO will uncomment these later once the files are unified

//TODO turn into a module so that we can import it in main.py

/* more or less the grammar we're parsing
<P>             ::= <expr>
<expr>          ::= <unary-op> | <binary-op> | <variable-op> | <digits>
<unary-op>      ::= (<unary> <expr>)
<binary-op>     ::= (<binary> <expr> <expr>)
<variable-op>   ::= (<variable> <expr-list>)
<expr-list>     ::= <expr> | <expr> <expr-list>
<unary>         ::= abs | sqrt | ceil
<binary>        ::= modulo | expt
<variable>      ::= min | max | + | * | - | /
<digits>        ::= <digit> | <digit> <digits>
<digit>         ::= 1 | 2 | .. | 9
*/

//define the possible token types as an enum
datatype TokenType = LEFT_PAREN | RIGHT_PAREN | DOT | MINUS | PLUS | STAR | SLASH 
                     | UNARY_OP | BINARY_OP | VARIABLE_OP | NUMBER | EOF

//define the possible operations that have identifiers longer than a single character
datatype BuiltInOp = ABS | SQRT | CEIL | MODULO | EXPT | MIN | MAX

//tokens are specific type of tuples
datatype Token = Pair(token_type:TokenType, token_value:string)

//nodes of the AST come from the grammar
datatype Expr = Number(value: string)
              | UnaryOp(op: string, arg: Expr)
              | BinaryOp(op:string, arg1: Expr, arg2: Expr)
              | VariableOp(op: string, arg1: Expr, argList: seq<Expr>)

//result datatype will either allow us to store a value or it will report an error/failure
//has to be generic so we can store Expr or Token
datatype Result<T> = Ok(data: T) | Err(error: string)

//helper functions
//true if the token provided represents a valid unary operation
function isUnaryOp(operationType: TokenType, operationValue: string) : bool
{
    operationType == TokenType.UNARY_OP &&
    (operationValue == "abs" || operationValue == "sqrt" || operationValue == "ceil")
}
//true if the token provided represents a valid binary operation
function isBinaryOp(operationType: TokenType, operationValue: string) : bool
{
    operationType == TokenType.BINARY_OP &&
    (operationValue == "modulo" || operationValue == "expt")
}
//true if the token provided represents a valid variable-argument operation
function isVariableOp(operationType: TokenType) : bool
{
    operationType == TokenType.VARIABLE_OP ||
    operationType == TokenType.PLUS ||
    operationType == TokenType.STAR ||
    operationType == TokenType.SLASH ||
    operationType == TokenType.MINUS
}
//true if the string provided is a valid operation in the language
function isValidOp(operationValue: string): bool{
    operationValue == "+" || operationValue == "-" ||
    operationValue == "*" || operationValue == "/" ||
    operationValue == "abs" || operationValue == "ceil" ||
    operationValue == "modulo" || operationValue == "expt" ||
    operationValue == "min" || operationValue == "max"
}

//helper predicates
//TODO
predicate ValidSubexpression(expr: Expr){
    true
}
predicate ValidSubexpressions(exprs: seq<Expr>)
{
    forall i :: 0 <= i < |exprs| ==> ValidSubexpression(exprs[i])
}

//helper methods
//peek ahead by a single token, but do not consume it
//if there are no more tokens, return EOF
method peekToken(tokens: seq<Token>, current_idx: int) returns (result: Token)
requires 0 <= current_idx <= |tokens|
ensures current_idx < |tokens| ==> result == tokens[current_idx]
//if idx is out of bounds, just return EOF
ensures current_idx == |tokens| ==> result.token_type == TokenType.EOF {
    if current_idx == |tokens|{
        var res := Pair(TokenType.EOF, "EOF");
        return res;
    }
    result := tokens[current_idx];
}


//-------------------------------PARSING--------------------------------
//transform a set of tokens into an AST
//returns Err if expression is invalid, otherwise returns Ok containing the AST root
method parse(tokens: seq<Token>) returns (result: Result<Expr>)
//preconditions
//list of tokens should be nonempty
//the lexer should add at least the EOF token at the end
requires |tokens| > 0
//it must either parse the expression, or return an error
ensures result.Ok? || result.Err?
//TODO ensures WellFormed(result)
//TODO if tokens has mismatched parens, then must return err
//TODO other properties of tokens and what result they imply
//TODO length of N tokens => depth of tree or length of tree should never exceed some value, depth of paren relation to pairs of parenthesis
//TODO maybe under what circumstance does it return an error? e.g. input token string is syntactically correct => can parse
//TODO explore adding start_idx, end_idx to expr datatype -> link to tokens constituting the expression
//TODO what else should parsers ensure?
//TODO think about reach goal => actually verify full functional correctness about the parser
//
//this is kind of like return True? what to verify here?
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
    //TODO prove this
    assume {:axiom} end_idx == |tokens|;
    assert end_idx == |tokens|;

    return ast;
}

//return an expression representing a number
method number(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
//our current idx should not be at the end of the list of tokens
requires 0 <= current_idx < |tokens|
//current token should be a number
requires tokens[current_idx].token_type == TokenType.NUMBER
//ensure that we consumed just the number token 
ensures end_idx == current_idx + 1
//end index should still be in bounds
ensures 0 <= end_idx <= |tokens|
decreases |tokens| - current_idx 
{
    //verify that the current token is a valid number token
    //TODO

    //no other parsing needed than this
    var parsed_num: Expr := Number(tokens[current_idx].token_value);
    return Ok(parsed_num), current_idx + 1;
}

//parse an expression
method expr(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
//should be at least one token to parse
requires |tokens| > 0
//current_idx must be in bounds
requires 0 <= current_idx < |tokens|
//after parsing, end_idx should be within [0, len(tokens)]
//ensures 0 <= end_idx <= |tokens|
//if we can parse the expression, the current_idx pointer must increase
ensures result.Ok? ==> end_idx > current_idx
decreases |tokens| - current_idx, 0
{
    //get next token in list
    var next_token: Token := tokens[current_idx];
    var token_type := next_token.token_type;

    //if the expression is a number, parse it
    if token_type == TokenType.NUMBER{
        var parsed_num, end_idx:= number(tokens, current_idx);
        return parsed_num, end_idx;
    }

    //otherwise token is an expression
    //subexpression should always start with '(', otherwise it's not a valid subexpression, e.g. "(+ 1 + 2 3)"
    //verify that the token we are going to consume is a left paren
    if next_token.token_type != TokenType.LEFT_PAREN{
        //consume the invalid token, then return an error
        var next_idx := current_idx + 1;
        return Err("invalid expression"), next_idx;
    }
    //consume left parenthesis
    var next_idx := current_idx + 1;

    //check if the subexpression ends after the left parenthesis, e.g. "(+ 1 2 ("
    if next_idx >= |tokens|{
        return Err("unexpected end of file"), next_idx;
    }

    //parse the operation for expression
    result, end_idx := op(tokens, next_idx);
}

//dispatch to one of the operation-parsing functions based on token type
method op(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
//should be at least one token
requires |tokens| > 0
//current_idx should be in bounds before parsing
requires 0 <= current_idx < |tokens|
//parser consumed at least one token
//ensures current_idx < end_idx <= |tokens|
//if we can parse the operation, current_idx must increase
ensures result.Ok? ==> end_idx > current_idx
decreases |tokens| - current_idx, 1
{
    //starting token should be an operation 
    //extract the operation type from the current token
    var operation_type: TokenType := tokens[current_idx].token_type;
    var operation_value: string := tokens[current_idx].token_value;

    //consume the operator
    var next_idx := current_idx + 1;

    //verify that the next token is a valid operation token
    if !isValidOp(operation_value){
        return Err("unknown operation"), next_idx;
    }
    //if there are no tokens after operator, invalid expression, e.g. "(+ 1 2 (+"
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), next_idx;
    }

    //dispatch to appropriate parsing functon based on the operation type
    if operation_type == TokenType.UNARY_OP{
        result, end_idx := unaryOp(tokens, next_idx, operation_value);
    }
    else if operation_type == TokenType.BINARY_OP{
        result, end_idx := binaryOp(tokens, next_idx, operation_value);
    }
    else if isVariableOp(operation_type) {
        result, end_idx := variableOp(tokens, next_idx, operation_value);
    }
    else{
        result, end_idx := Err("invalid operation"), current_idx + 1;
    }

}

//parse a single unary operation
method unaryOp(tokens: seq<Token>, current_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
//at least one token to parse
requires |tokens| > 0
//current_idx is in bounds
requires 0 <= current_idx < |tokens|
//after parsing, end_idx is still in bounds
//ensures current_idx < end_idx <= |tokens|
//if we can parse the unary operation, current_idx must increase
ensures result.Ok? ==> end_idx > current_idx
decreases |tokens| - current_idx, 2
{
    //verify that it is a valid unary op
    //TODO maybe put this in the preconditions?

    //|tokens| - current_idx should have been decreased by this point

    //parse the expression after the operator
    var parsed_subexpr, next_idx := expr(tokens, current_idx);
    
    //check if parsing the subexpression fails
    if parsed_subexpr.Err?{
        return parsed_subexpr, next_idx;
    }
    //check if the expression ends without a right_paren, e.g. (+ 1 2 (* 3 4)
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), next_idx;
    }
    //next token should be a right paren
    if tokens[next_idx].token_type != TokenType.RIGHT_PAREN{
        return Err("missing RIGHT_PAREN"), next_idx;
    }

    //the operation can be parsed
    var parsed_unary_op := Ok(UnaryOp(operation, parsed_subexpr.data));

    //consume right parenthesis
    //return parsed unary op
    result, end_idx := parsed_unary_op, next_idx + 1;
}

//TODO parse a single binary operation starting at token with index current_idx
method binaryOp(tokens: seq<Token>, current_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
//should be at least one token to parse
requires |tokens| > 0
//current_idx should be in bounds
requires 0 <= current_idx < |tokens|
//after parsing, end_idx should be in bounds
//ensures current_idx < end_idx <= |tokens|
//if we can parse the binary operation, the index pointer must increase
ensures result.Ok? ==> end_idx > current_idx
decreases |tokens| - current_idx, 2
{

    //verify the operator is a binary op
    //TODO maybe put in preconditions

    //parse the first subexpressions after the operator
    var parsed_subexpr_1: Result<Expr>, next_idx: int;
    parsed_subexpr_1, next_idx := expr(tokens, current_idx);

    //check if parsing the subexpression fails
    if parsed_subexpr_1.Err?{
        return parsed_subexpr_1, next_idx;
    }
    //check if the first subexpression ends without a right_paren, e.g. "(+ 1 (ceil 4.5" 
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), next_idx;
    }

    assert next_idx < |tokens|;

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
        return Err("missing RIGHT_PAREN"), next_idx;
    }

    //consume right parenthesis
    next_idx := next_idx + 1;

    //make a binary operation using the current operation and two parsed subexpressions
    var parsed_binary_op := BinaryOp(operation, parsed_subexpr_1.data, parsed_subexpr_2.data);

    //return parsed binary operation
    result, end_idx := Ok(parsed_binary_op), next_idx;
}

//TODO parse a single variable-param operation starting at token with index current_idx
method variableOp(tokens: seq<Token>, current_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
//should be at least one token to parse
requires |tokens| > 0
//current_idx should be valid
requires 0 <= current_idx < |tokens|
//after parsing, should be at the end of the expression or in bounds 
//ensures current_idx < end_idx <= |tokens|
//if the operation can be parsed, current_idx must increase
ensures result.Ok? ==> end_idx > current_idx 
decreases |tokens| - current_idx, 2
{
    //verify the current token is a variable-argument operator
    //TODO maybe put in preconditions?
    //(+ 1 2 3)
    //required to have at least one subexpression after operator
    var parsed_required_subexpression: Result<Expr>, next_idx: int;

    //parse required expressions after operator
    parsed_required_subexpression, next_idx := expr(tokens, current_idx);
    if parsed_required_subexpression.Err?{
        return parsed_required_subexpression, current_idx;
    }
    //check if the required subexpression ends without a right_paren, e.g. "(+ 1 2 (* 3 4"
    if next_idx >= |tokens|{
        return Err("unexpected EOF"), next_idx;
    }

    //populate argument list with any remaining arguments
    var subexprList: seq<Expr> := [];

    //look ahead to next token
    //if it is a RIGHT_PARENT, end of expression. loop terminates
    //otherwise, keep parsing subexpressions and adding to list
    var nextToken: Token := peekToken(tokens, next_idx);

    //(+ 1 2 3 4)
    while nextToken.token_type != TokenType.RIGHT_PAREN
    //current_idx is always in bounds
    invariant 0 <= current_idx < |tokens|
    //current_idx pointer always gets closer to the end of the token sequence
    decreases |tokens| - next_idx, 2
    {
        //parse next subexpr
        var next_parsed_subexpr: Result<Expr>;

        //TODO prove this
        //ensure that we are not at the end of the expression prematurely
        if next_idx >= |tokens|{
            return Err("unexpected EOF"), next_idx;
        }

        next_parsed_subexpr, next_idx := expr(tokens, next_idx);

        //check if subexpression can't be parsed
        if next_parsed_subexpr.Err?{
            return next_parsed_subexpr, next_idx;
        }

        //add to list of arguments
        subexprList := subexprList + [next_parsed_subexpr.data];

        //move to next token in expression
        nextToken := peekToken(tokens, current_idx);
    }

    var parsed_variable_op := VariableOp(operation, parsed_required_subexpression.data, subexprList);

    //consume right parenthesis
    next_idx := next_idx + 1;

    //return parsed variable-argument operation
    result, end_idx := Ok(parsed_variable_op), next_idx;
}

method main()
requires true
ensures true
{
    //TODO add something here
}