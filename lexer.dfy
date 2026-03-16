include "types.dfy" //contains all the custom types we're using


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
requires forall i :: 0<=i<|tok| ==> tok[i].token_value==tok2[i].token_value
ensures Flatten(tok)==Flatten(tok2)
{

}

/*predicate matchesString(str: seq<char>,tokenized: seq<Token>){
    forall i :: 0<=i<|str| ==> 
    (
        
    )
}*/
predicate ValidUnary(tok: Token){
    tok.token_value=="abs" || tok.token_value=="sqrt" || tok.token_value=="ceil"
}
predicate ValidBinary(tok: Token){
    tok.token_value=="modulo" || tok.token_value=="expt"
}
predicate ValidVarOp(tok: Token){
    tok.token_value=="min" || tok.token_value=="max"
}
predicate ValidNumber(tok: Token){
    forall i::0<=i<|tok.token_value| ==>(
        (tok.token_value[i] as int >=48 && tok.token_value[i] as int  <=57)
        || tok.token_value[i]=='.'
    )
}
predicate validValue(tok: Token){
    (tok.token_type==UNARY_OP ==> ValidUnary(tok)) &&
    (tok.token_type==BINARY_OP ==> ValidBinary(tok)) &&
    (tok.token_type==VARIABLE_OP ==> ValidVarOp(tok)) &&
    (tok.token_type==NUMBER ==> ValidNumber(tok)) &&
    (tok.token_type==PLUS ==> tok.token_value=="+") &&
    (tok.token_type==MINUS ==> tok.token_value=="-") &&
    (tok.token_type==STAR ==> tok.token_value=="*") &&
    (tok.token_type==SLASH ==> tok.token_value=="/") &&
    (tok.token_type==LEFT_PAREN ==> tok.token_value=="(") &&
    (tok.token_type==RIGHT_PAREN ==> tok.token_value==")")
}

method lex(str: seq<char>) returns (tokenized: Result<seq<Token>>)
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
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (validtype(tokenized.data[i]))

//ensures all tokens are valid and correct type
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (
    validValue(tokenized.data[i])
)

//ensures all characters are represented in order in tokens
ensures tokenized.Ok? ==> Flatten(tokenized.data)==str

{
    var i:=0;
    //var tokpos:=0;
    var tok: seq<Token> := [];
    while i<|str|
    invariant forall i:: 0<=i<|tok| ==> (validtype(tok[i]) ||tok[i].token_type==TEMPSTRING)
    invariant i<=|str|
    invariant forall i:: 0<=i<|tok| ==> validValue(tok[i])
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
        assert validValue(tok[|tok|-1]);
        i:=i+1;
        //assert Flatten(tok)==str[0..i];
        //assert forall i:: 0<=i<|tok| ==> validValue(tok[i]);
    }
    //specifying strings
    i:=0;
    //assert i<=|tok|;
    assert forall i:: 0<=i<|tok| ==> (validtype(tok[i]) ||tok[i].token_type==TEMPSTRING);
    assert Flatten(tok)==str;
    ghost var a:=tok;

    while i<|tok|
    invariant i<=|tok|
    invariant forall j:: 0<=j<|tok| ==> validValue(tok[j])
    invariant forall j:: 0<=j<|tok| ==> (validtype(tok[j]) ||tok[j].token_type==TEMPSTRING)
    invariant forall j:: 0<=j<i ==> ((validtype(tok[j])))
    invariant |a|==|tok|
    invariant forall j:: 0<=j<|tok| ==> a[j].token_value==tok[j].token_value
    invariant Flatten(tok)==str
    {
        //ghost var a:=tok[i];
        //assert validtype(tok[i]) || tok[i].token_type==TEMPSTRING;
        if(tok[i].token_type==TEMPSTRING){ //if token is string
            
            if(ValidUnary(tok[i])){
                
                tok := tok[i :=
                Pair(UNARY_OP,tok[i].token_value)];
                
            }
            else if(ValidBinary(tok[i])){
                tok := tok[i :=
                Pair(BINARY_OP,tok[i].token_value)];
            }
            else if(ValidVarOp(tok[i])){
                tok := tok[i :=
                Pair(VARIABLE_OP,tok[i].token_value)];
            }
            else{
                return Err("invalid string");
            }   
        }
        assert a[i].token_value==tok[i].token_value;
        Flatsame(tok,a);
        assert validtype(tok[i]);
        //assert tok[i].token_type==UNARY_OP ==> ValidUnary(tok[i]);
        i:=i+1;
    }
    return Ok(tok);
}

/*match result_var
           case Ok => do something;
           case Err => do something else;*/
