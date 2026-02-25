include "fileio.dfy"

//need to define a tuple type that hold (token_type, token_value) pairs
datatype Pair = Pair(fst:string, snd:string)

//transform user input into a set of tokens
//replace '(' with ' ( '
//replace ')' with ' ) '
method lex(s: string) //returns (tokens: seq<string>)
requires true
ensures true
{
    //TODO implement
    assume(false);
}

//unit tests for lexing
method testLex()
requires true
ensures true
{
    //TODO implement
    assume(false);
}


//add type tags to all of the tokens before passing to parser
method tag(tokens: seq<string>) returns (tagged_tokens: seq<Pair>)
requires true
ensures true
{
    //TODO implement
    assume(false);
}

//unit tests for tagging
method testTag()
requires true
ensures true
{
    //TODO implement
    assume(false);
}


//transform a set of tokens into an AST
//returns Failure if expression is invalid
    //e.g. parentheses don't match
    //e.g. wrong number of operands for a given operation
    //etc
method parse(tokens: seq<string>) returns (ast: seq<Pair>)
requires true
ensures true
{
    //TODO implement
    assume(false);
}

//unit tests for parsing
method testParse()
requires true
ensures true
{
    //TODO implement
    assume(false);
}

method main()
requires true
ensures true
{
    //so..funny story. dafny doesn't actually support taking in input or producing simple output.
    //from the Dafny documentation FAQ
    /*
        Question
        How do I read a file as a string?
    
        Answer
        You can’t in pure Dafny. Not yet. Such a capability will eventually be part of a standard IO library.

        What you can do is to write such a function in another language, say Java, and then use it in Dafny by extern declarations.
    */
    //maybe we can do this and then add some python interface that extends the functionality like he was talking about in lecture
    //I would imagine that we can create some python file like main.py, then import the needed function
    //from the transpiled parser.py file.
    assume(false);
}