datatype TokenType = LEFT_PAREN | RIGHT_PAREN | DOT | MINUS | PLUS | STAR | SLASH 
                     | UNARY_OP | BINARY_OP | VARIABLE_OP | NUMBER | EOF | TEMPSTRING

datatype Token = Pair(token_type:TokenType, token_value:string)


predicate validtype(token: Token){
    token.token_type==LEFT_PAREN ||
    token.token_type==RIGHT_PAREN ||
    token.token_type==MINUS ||
    token.token_type==PLUS ||
    token.token_type==STAR ||
    token.token_type==SLASH ||
    token.token_type==NUMBER ||
    token.token_type==UNARY_OP ||
    token.token_type==BINARY_OP ||
    token.token_type==VARIABLE_OP ||
    token.token_type==EOF
}
function Flatten(tok: seq<Token>): seq<char>
{
    if |tok|==0 then []
    else Flatten(tok[0..|tok|-1])+tok[|tok|-1].token_value
  
}
lemma Flatsame(tok: seq<Token>,tok2: seq<Token>)
requires |tok|==|tok2|
requires forall i :: 0<=i<|tok| ==> tok[i].token_value==tok2[i].token_value;
ensures Flatten(tok)==Flatten(tok2);
{

}

/*predicate matchesString(str: seq<char>,tokenized: seq<Token>){
    forall i :: 0<=i<|str| ==> 
    (
        
    )
}*/

method Lex(str: seq<char>) returns (tokenized: seq<Token>)
requires forall i::0<=i<|str| ==> (
(str[i] as int >=48 && str[i] as int  <=57) ||
str[i]=='+' ||
str[i]=='-' ||
str[i]=='*' ||
str[i]=='/' ||
str[i]=='(' ||
str[i]==')'
)


//ensures no tempstrings
ensures forall i:: 0<=i<|tokenized| ==> (validtype(tokenized[i]))

//ensures all tokens are valid and correct type
//ensures all characters are represented in order in tokens
ensures Flatten(tokenized)==str;

{
    var i:=0;
    //var tokpos:=0;
    var tok: seq<Token> := [];
    while i<|str|
    invariant forall i:: 0<=i<|tok| ==> (validtype(tok[i]) ||tok[i].token_type==TEMPSTRING)
    invariant i<=|str|
    invariant Flatten(tok)==str[0..i]
    {
        //numbers
        if ((str[i] as int >=48 && str[i] as int  <=57) || str[i]=='.'){
            if(|tok|>=1 && tok[|tok|-1].token_type==NUMBER){ //if last is number
                tok := tok[|tok|-1 :=   //add digit
                Pair(NUMBER,tok[|tok|-1].token_value+[str[i]])];
            }
            else{
                tok:=tok + [Pair(NUMBER,[str[i]])];
            }
        }
        //letters 97 to 122
        else if (str[i] as int >=97 && str[i] as int  <=122){
            if(|tok|>=1 && tok[|tok|-1].token_type==TEMPSTRING){ //if last is number
                tok := tok[|tok|-1 :=   //add letter
                Pair(NUMBER,tok[|tok|-1].token_value+[str[i]])];
            }
            else{
                tok:=tok + [Pair(TEMPSTRING,[str[i]])];
            }
        }
        //basic symbols
        else{
            if(str[i]=='+'){
                tok:=tok + [Pair(PLUS,"+")];
            }
            else if(str[i]=='-'){
               tok:=tok + [Pair(MINUS,"-")];
            }
            else if(str[i]=='*'){
               tok:=tok + [Pair(STAR,"*")];
            }
            else if(str[i]=='/'){
               tok:=tok + [Pair(SLASH,"/")];
            }
            else if(str[i]=='('){
               tok:=tok + [Pair(LEFT_PAREN,"(")];
            }
            else if(str[i]==')'){
               tok:=tok + [Pair(RIGHT_PAREN,")")];
            }
            //tokpos:=tokpos+1;
            //num==0;
        }
        assert validtype(tok[|tok|-1]) || tok[|tok|-1].token_type==TEMPSTRING;
        i:=i+1;
    }
    //specifying strings
    i:=0;
    //assert i<=|tok|;
    assert forall i:: 0<=i<|tok| ==> (validtype(tok[i]) ||tok[i].token_type==TEMPSTRING);
    assert Flatten(tok)==str;
    ghost var a:=tok;

    while i<|tok|
    invariant i<=|tok|
    invariant forall i:: 0<=i<|tok| ==> (validtype(tok[i]) ||tok[i].token_type==TEMPSTRING);
    invariant forall j:: 0<=j<i ==> ((validtype(tok[j])))
    invariant |a|==|tok|
    invariant forall i:: 0<=i<|tok| ==> a[i].token_value==tok[i].token_value;
    invariant Flatten(tok)==str
    {
        //ghost var a:=tok[i];
        //assert validtype(tok[i]) || tok[i].token_type==TEMPSTRING;
        if(tok[i].token_type==TEMPSTRING){ //if token is string
            
            if(tok[i].token_value=="abs" || tok[i].token_value=="sqrt" || tok[i].token_value=="ceil"){
                
                tok := tok[i :=
                Pair(UNARY_OP,tok[i].token_value)];
                
            }
            else if(tok[i].token_value=="modulo" || tok[i].token_value=="expt"){
                tok := tok[i :=
                Pair(BINARY_OP,tok[i].token_value)];
            }
            else if(tok[i].token_value=="min" || tok[i].token_value=="max"){
                tok := tok[i :=
                Pair(VARIABLE_OP,tok[i].token_value)];
            }
            else{
                //REMOVE THIS LATER
                tok := tok[i :=
                Pair(VARIABLE_OP,tok[i].token_value)];
            }   
        }
        assert a[i].token_value==tok[i].token_value;
        Flatsame(tok,a);
        assert validtype(tok[i]);
        i:=i+1;
    }
    return tok;
}

/*match result_var
           case Ok => do something;
           case Err => do something else;*/
