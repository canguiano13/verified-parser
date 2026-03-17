import sys
import module_ as lexerparser
import _dafny

#convert a dafny sequence into a string
#thanks claude
def seq_to_str(seq):
    return ''.join(seq)

#print output
#ast is a nested tree structure with a root expression and one or more subexpressions
def pretty_print(ast, factor=1, root_print=True):
    indent = "" * factor

    if ast.is_Number:
        num = seq_to_str(ast.value)
        return f"{indent}{num}"

    elif ast.is_UnaryOp:
        op = seq_to_str(ast.op)
        arg = pretty_print(ast.arg, factor + 1)
        return f"{indent}({op}\n{arg}\n)"

    elif ast.is_BinaryOp:
        op = seq_to_str(ast.op)
        arg1 = pretty_print(ast.arg1, factor + 1)
        arg2 = pretty_print(ast.arg2, factor + 1)
        return f"{indent}({op}\n{arg1}\n{arg2}\n)"

    elif ast.is_VariableOp:
        op = seq_to_str(ast.op)
        required_arg = pretty_print(ast.arg1, factor + 1)

        args = [required_arg]
        for arg in ast.argList:
            args.append(pretty_print(arg, factor + 1))
        
        formatted_args = "\n".join(args)
        return f"{indent}({op}\n{formatted_args}\n)"

    else:
        error("Error while printing")

#print an error message and exit immediately
def error(message):
    sys.stderr.write(f"Error: {message}\n")
    sys.stderr.write(f"Example usage: python3 main.py \"(+ 1 2 (- 4 3))\"\n")
    sys.exit(1)

def main():
    #throw an error if the user doesn't provide the expression
    if len(sys.argv) <= 1:
        error("Please provide an expression to parse")

    #get the expression to parse from the user
    expr = sys.argv[-1]
    if len(expr) == 0:
        error("Unexpected EOF")

    #lex the tokens from the user's expression
    lex_result = lexerparser.default__.lex(expr)
    #if can't lex, print the error
    if lex_result.is_Err:
        error(seq_to_str(lex_result.error))
    tokens = lex_result.data

    #parse the tokens derived into an AST
    parse_result = lexerparser.default__.parse(tokens)
    #if can't parse, print the error
    if parse_result.is_Err:
        error(seq_to_str(parse_result.error))

    ast = parse_result.data
    print(pretty_print(ast))


if __name__ == "__main__":
    main()
