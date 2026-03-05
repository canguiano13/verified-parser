//#include "test.dfy" 
//include "lexer.dfy" //TODO will uncomment these later once the files are unified

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
              | VariableOp(op: string, arg1: Expr, arg2: Expr, argList: seq<Expr>)

//result datatype will either allow us to store a value
//or it will produce an error/failure
//has to be generic so we can store Expr or Token
datatype Result<T> = Ok(data: T) | Err(error: string)

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
    assume{:axiom} 0 <= current_idx < |tokens|;
    assume{:axiom} current_idx == |tokens| - 1;

    //make sure that after parsing ends, the last token is EOF
    //TODO not sure if we need to even do this
    if tokens[current_idx].token_type != TokenType.EOF{
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
ensures current_idx < end_idx //<= |tokens| //<-- TODO do we want this to hold
decreases |tokens| - current_idx //think this fixes the termination issue
//TODO add ensures
{
    //shadow current_idx
    var current_idx := current_idx;

    //get start at the next token
    var next_token: Token := tokens[0];
    var token_type := next_token.token_type;
    var token_val := next_token.token_value;

    //expression can be just a number
    if token_type == TokenType.NUMBER{
        result, end_idx := number(tokens, current_idx);
    }
    //parse some operation
    else if token_type == TokenType.LEFT_PAREN{
        //consume left parenthesis to get to operation
        current_idx := current_idx + 1;

        //will need this to pass
        //TODO need to prove that current_idx + 1 <= |tokens|
        //maybe use the advance_idx function somehow?
        assume{:axiom} current_idx < |tokens|;
        assert current_idx < |tokens|;

        result, end_idx := op(tokens, current_idx);
    }
    //unrecognized token
    else{
        return Err("unrecognized expression"), current_idx + 1;
    }
}

//consume the token at the current_idx
//this token represents a number
method number(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
//ensure that we consumed just the single token
ensures end_idx == current_idx + 1
decreases |tokens| - current_idx 
{
    //no other parsing needed than this
    var parsed_num: Expr := Number(tokens[current_idx].token_value);
    return Ok(parsed_num), current_idx + 1;
}

//TODO +, *, / operations are currently being lexed as PLUS, STAR, and SLASH due to the reference
//could update lexer to just tag them all as variable ops
//that would make this function unnecessary
function isVariableOp(operationType: TokenType) : bool
//requires ...
//ensures ...
{
    operationType == TokenType.VARIABLE_OP ||
    operationType == TokenType.PLUS ||
    operationType == TokenType.STAR ||
    operationType == TokenType.SLASH
}

//TODO dispatch to one of the operation-parsing functions based on token type
method op(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
//TODO might have to require this
//requires current_idx < |tokens| - 2
//ensure that we consumed at least one token
ensures end_idx > current_idx
ensures end_idx <= |tokens| + 1
decreases |tokens| - current_idx
{
    var tokens := tokens;
    var current_idx := current_idx;

    //extract two parts parts of th
    var operation_type: TokenType := tokens[current_idx].token_type;
    var operation_value: string := tokens[current_idx].token_value;

    //TODO need to fix decreases clause because the program doesn't think our program terminate
    if operation_type == TokenType.MINUS{
        result, end_idx := minus(tokens, current_idx);
    }
    else if operation_type == TokenType.UNARY_OP{
        result, end_idx := unaryOp(tokens, current_idx, operation_value);
    }
    else if operation_type == TokenType.BINARY_OP{
        result, end_idx := binaryOp(tokens, current_idx, operation_value);
    }
    else if isVariableOp(operation_type) {
        result, end_idx := variableOp(tokens, current_idx, operation_value);
    }
    else{
        result, end_idx := Err("invalid operation"), current_idx + 1;
    }

}

//TODO parse a single unary operation starting at token with index current_idx
method unaryOp(tokens: seq<Token>, current_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
ensures end_idx <= |tokens| + 1
decreases |tokens| - current_idx //i think this fixes the termination issue?
{
    //parse the expression after the operator
    var parsed_subexpr, current_idx := expr(tokens, current_idx);

    //check if parsing the subexpression fails
    if parsed_subexpr.Err?{
        return parsed_subexpr, current_idx;
    }

    //else successfully parsed
    var parsed_unary_op := Ok(UnaryOp(operation, parsed_subexpr.data));

    //consume right parenthesis
    current_idx := current_idx + 1;

    //return parsed unary op
    result, end_idx := parsed_unary_op, current_idx;
}

//TODO parse a single binary operation starting at token with index current_idx
method binaryOp(tokens: seq<Token>, current_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
ensures end_idx <= |tokens| + 1
decreases |tokens| - current_idx
{
    var current_idx := current_idx;
    var parsed_subexpr_1: Result<Expr>, parsed_subexpr_2: Result<Expr>;

    //parse the first expression after the operator
    parsed_subexpr_1, current_idx := expr(tokens, current_idx);
    //return error immediately if the subexpresion cannot be parsed
    if parsed_subexpr_1.Err?{
        return parsed_subexpr_1, current_idx;
    }

    assume{:axiom} current_idx < |tokens|;
    //parse the second expression after the operator
    parsed_subexpr_2, current_idx := expr(tokens, current_idx);
    //return error immediately if second subexpression cannot be parsed
    if parsed_subexpr_2.Err?{
        return parsed_subexpr_2, current_idx;
    }

    //make a binary operation using the current operation
    var parsed_binary_op := BinaryOp(operation, parsed_subexpr_1.data, parsed_subexpr_2.data);

    //consume right parenthesis
    current_idx := current_idx + 1;

    //return parsed binary operation
    result, end_idx := Ok(parsed_binary_op), current_idx;
}

//TODO parse a single variable-param operation starting at token with index current_idx
method variableOp(tokens: seq<Token>, current_idx: int, operation: string) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
ensures end_idx <= |tokens| + 1
decreases |tokens| - current_idx
{
    //shadow current_idx
    var current_idx := current_idx;
    var parsed_subexpr_1: Result<Expr>, parsed_subexpr_2: Result<Expr>; 


    //parse two required expressions after operator
    parsed_subexpr_1, current_idx := expr(tokens, current_idx);
    if parsed_subexpr_1.Err?{
        return parsed_subexpr_1, current_idx;
    }

    parsed_subexpr_2, current_idx := expr(tokens, current_idx);
    if parsed_subexpr_2.Err?{
        return parsed_subexpr_2, current_idx;
    }

    //populate list of any remaining arguments
    var subexprList: seq<Expr> := [];
    //TODO figure out this loop
    // while false
    // invariant false
    // {
    //     //parse remaining args
    //     //look ahead to next token
    //     //if it is a RIGHT_PARENT, end of expression. loop terminates
    //     //otherwise, keep parsing subexpressions and adding to list
    // }

    var parsed_variable_op := VariableOp(operation, parsed_subexpr_1.data, parsed_subexpr_2.data, subexprList);

    //consume right parenthesis
    current_idx := current_idx + 1;

    //return parsed variable-argument operation
    result, end_idx := Ok(parsed_variable_op), current_idx;
}

//TODO parse an operation using the minus operator
//either has to be subtraction or negation
method minus(tokens: seq<Token>, current_idx: int) returns (result: Result<Expr>, end_idx: int)
requires |tokens| > 0
requires 0 <= current_idx < |tokens|
ensures end_idx > current_idx
decreases |tokens| - current_idx
//TODO add ensures
{
    //shadow current_idx
    var current_idx := current_idx;
    var parsed_subexpr_1: Result<Expr>;
    var operation := "-";

    //check if it is a unary op or
    //parse required subexpr after operator
    parsed_subexpr_1, current_idx := expr(tokens, current_idx);
    if parsed_subexpr_1.Err?{
        return parsed_subexpr_1, current_idx;
    }
    
    var is_unary_op: bool;
    is_unary_op := true; //TODO replace with a condition checking if the token from peek() is a RIGHT_PAREN

    //peek ahead to the next token to see if it's a number or right parenthesis
    //need to check that we're not yet at the end of the list already to do a safe peek
    //peek()

    //if it's a unary expression
    if is_unary_op{ 
        //consume right parenthesis
        current_idx := current_idx + 1;

        return Ok(UnaryOp(operation, parsed_subexpr_1.data)), current_idx;
    }

    //otherwise it's a variable-argument expression
    //parse the other required subexpression
    var parsed_subexpr_2: Result<Expr>;
    parsed_subexpr_2, current_idx := expr(tokens, current_idx);
    if parsed_subexpr_2.Err?{
        return parsed_subexpr_2, current_idx;
    }

    //populate list of any remaining arguments
    var subexprList: seq<Expr> := [];
    //TODO figure out this loop
    // while false
    // condition will be something like while peek(tokens, current_idx).token_type != TokenType.RIGHT_PAREN
    // invariant false
    // {
    //     //parse remaining args
    // }

    var parsed_variable_op := VariableOp(operation, parsed_subexpr_1.data, parsed_subexpr_2.data, subexprList);
    return Ok(parsed_variable_op), current_idx;
}


method main()
requires true
ensures true
{
    //TODO add something here maybe?
}