import sys
import module_ as lexerparser
import _dafny

#convert a dafny sequence into a string
#need this since dafny strings are internally character sequences (seq<char>)
#thanks claude
def seq_to_str(seq):
    return ''.join(seq)

#print output
#ast is a nested tree structure with a root expression and one or more subexpressions
def pretty_print(ast, factor=0, root_print=True):
    #let's use two spaces instead of a tab
    indent = "  " * factor
    left_paren = f"{indent}("
    right_paren= f"{indent})"

    if ast.is_Number:
        num = f"{indent}{seq_to_str(ast.value)}"
        return num

    elif ast.is_UnaryOp:
        op = seq_to_str(ast.op)
        arg = pretty_print(ast.arg, factor + 1)
        return f"{left_paren}{op}\n{arg}\n{right_paren}"

    elif ast.is_BinaryOp:
        op = seq_to_str(ast.op)
        arg1 = pretty_print(ast.arg1, factor + 1)
        arg2 = pretty_print(ast.arg2, factor + 1)
        return f"{left_paren}{op}\n{arg1}\n{arg2}\n{right_paren}"

    elif ast.is_VariableOp:
        op = seq_to_str(ast.op)
        required_arg = pretty_print(ast.arg1, factor + 1)

        args = [required_arg]
        for arg in ast.argList:
            args.append(pretty_print(arg, factor + 1))
        
        formatted_args = "\n".join(args)
        return f"{left_paren}{op}\n{formatted_args}\n{right_paren}"

    else:
        error("Error while printing")

#print an error message and exit immediately
def error(message):
    sys.stderr.write(f"Error: {message}\n")
    sys.exit(1)

def main():
    #throw an error if the user doesn't provide the expression
    if len(sys.argv) <= 1:
        sys.stderr.write(f"Example usage: python3 main.py \"(+ 1 2 (- 4 3))\"\n")
        error("Please provide an expression to parse")
        
    #get the expression to parse from the user
    expr = sys.argv[-1]
    if not isinstance(expr, str):
        error("bad expression")
        sys.stderr.write(f"Example usage: python3 main.py \"(+ 1 2 (- 4 3))\"\n")

    #lex the tokens from the user's expression
    lex_result = lexerparser.default__.lex(expr)
    #if can't lex, print the error
    if lex_result.is_Err:
        error(seq_to_str(lex_result.error))
    tokens = lex_result.data

    #parse the derived tokens into an AST
    parse_result = lexerparser.default__.parse(tokens)
    #if can't parse, print the error
    if parse_result.is_Err:
        error(seq_to_str(parse_result.error))

    ast = parse_result.data
    print(pretty_print(ast))


if __name__ == "__main__":
    main()
