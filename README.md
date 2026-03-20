# verified-parser
Formally verified parser for a small subset of LISP

## 0. Introduction
This project aims to explore formal verification in the context of compilers by implementing a parser for a subset of Lisp operations. The goal is to ensure that, when given a LISP expression, our parser can guarantee that an appropriate AST is produced for any valid expression, and guarantee that an appropriate error is produced for an invalid expression.

To achieve this, we implement formally verified functions in Dafny that first lex the user's expression into a series of tokens, then construct an Abstract Syntax Tree from those tokens.

Expressions containing the following operations are supported by the parser:
- +, -, /, %
- modulo
- abs
- sqrt
- expt
- ceil
- min, max
 
 The parser also supports both integers and floating-point numbers. The following expression is valid, for example:

 ```
 (+ (- 5 1) (/ 4 2) (abs (- (ceil 3.14))))
 ```

## 1. Prerequisites
This project uses Dafny to assist with formal verification, and Python as a driver for the I/O portions. Thus, you'll need to make sure that you have installed both. You can test this with the following terminal commands:

```
python3 --version
dafny --version
```

Instructions for installing Python and Dafny can be found at the following links:

- Python: https://www.python.org/downloads/
- Dafny: https://dafny.org/latest/Installation


If you haven't yet, be sure to also clone the repository via the following commands:
```
git clone https://github.com/canguiano13/verified-parser.git
cd verified-parser
```

## 2. Running the Parser

To start, run `build.sh`, which will build the Dafny project. This is required before you can start parsing expressions. This script has been tested on a machine running Ubuntu 24.04. If it fails to build the project, see **3. Manually Building**

```
./build.sh 
```

If successful, you will see a message telling you that the parser is ready to accept an expression:

```
Dafny program verifier finished with 17 verified, 0 errors
Build was successful. Try parsing an expression!
e.g. python3 main.py "(+ 1 2 (- 4 3))
```

Once it has been compiled, you can pass an expression via the command-line to our Python driver to initiate the lexing and parsing. The program will then print the produced AST (if your expression is valid), or it will print an error message (if your expression is invalid). For example the following invocation:

```
python3 main.py "(+ 1 2 (- 4 3))"
```

will produce the following AST:

```
(+
    1
    2
    (-
        4
        3
    )
)
```

If you changed any Dafny code and would like to rebuild the parser, first run the cleaning script:

```
./clean.sh
./build.sh
```

## 3. Manually Building
In the event the `./build.sh` script doesn't work for you, can also build using the following steps. First, verify the files we're going to build. This should report no errors.

```
dafny verify parser.dfy lexer.dfy types.dfy validation.dfy
```

Next, transpile the Dafny code into Python. This will make a module that we can connect our driver file to.

```
dafny build --target:py --output:parse_ast parser.dfy lexer.dfy types.dfy validate.dfy
```

Once this completes, you should see a folder named `parse_ast-py/` in your directory. Copy the driver into this directory with the name main.py, then `cd` into the new directory.

```
cp driver.py ./parse_ast-py/main.py
cd ./parse_ast-py
```

Now the parser is ready to accept an expression!

```
python3 main.py "(+ 1 2 (- 4 3))"
```
