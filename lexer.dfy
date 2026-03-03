
//TODO might be good to separate the lexing parts from the parsing parts

datatype TokenType = LEFT_PAREN | RIGHT_PAREN | DOT | MINUS | PLUS | STAR | SLASH 
                     | UNARY_OP | BINARY_OP | VARIABLE_OP | NUMBER | EOF

datatype Token = Pair(token_type:TokenType, token_value:string)

method Sum(str: seq<char>) returns (tokenized: seq<Token>)
requires forall i::0<=i<|str| ==> (
(str[i] as int >=48 && str[i] as int  <=57) ||
str[i]=='+' ||
str[i]=='-' ||
str[i]=='*' ||
str[i]=='/' ||
str[i]=='(' ||
str[i]==')'
)

{
    var i:=0;
    //var tokpos:=0;
    var tok: seq<Token> := [];
    while i<|str|{
        //numbers
        if (str[i] as int >=48 && str[i] as int  <=57){
            if(|tok|>=1 && tok[|tok|-1].token_type==NUMBER){ //if last is number
                tok := tok[|tok|-1 :=   //add digit
                Pair(NUMBER,tok[|tok|-1].token_value+[str[i]])];
            }
            else{
                tok:=tok + [Pair(NUMBER,[str[i]])];
            }
        }
        //basic symbols
        else{
            if(str[i]=='+'){
                tok:=tok + [Pair(PLUS,"idk?")];
            }
            else if(str[i]=='-'){
               tok:=tok + [Pair(MINUS,"idk?")];
            }
            else if(str[i]=='*'){
               tok:=tok + [Pair(STAR,"idk?")];
            }
            else if(str[i]=='/'){
               tok:=tok + [Pair(SLASH,"idk?")];
            }
            else if(str[i]=='('){
               tok:=tok + [Pair(LEFT_PAREN,"idk?")];
            }
            else if(str[i]==')'){
               tok:=tok + [Pair(RIGHT_PAREN,"idk?")];
            }
            //tokpos:=tokpos+1;
            //num==0;
        }
        i:=i+1;
    }
    return tok;
}
