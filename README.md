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
This project uses Dafny to assist with formal verification, and Python as a driver for the formally verified parts. Consequently, you'll need to make sure that you have installed both. You can test this with the following (Bash) commands:

```
python3 --version
dafny --version
```

Instructions for Python and Dafny can be found at the following links:

- Python: https://www.python.org/downloads/
- Dafny: https://dafny.org/latest/Installation

## 2. Running the Parser

To start, run `build.sh`, which will build the Dafny project into a Python module. This is required before you can start parsing expressions. This script has been tested on a machine running Ubuntu 24.04. If it fails to build the project, see **3. Troubleshooting**

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
(
    +
    1
    2
    (
        -
        4
        3
    )
)

```

Once you have finished using the parser, you can clean up unneeded files with our `clean.sh` script:

```
./clean.sh
```


