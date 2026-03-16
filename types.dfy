//only way I could think to get around the duplicate custom type declaration
//define the possible token types as an enum
datatype TokenType = LEFT_PAREN | RIGHT_PAREN | DOT | MINUS | PLUS | STAR | SLASH 
                     | UNARY_OP | BINARY_OP | VARIABLE_OP | NUMBER | EOF | TEMPSTRING

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