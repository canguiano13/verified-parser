datatype TokenType = LEFT_PAREN | RIGHT_PAREN | DOT | MINUS | PLUS | STAR | SLASH 
                     | UNARY_OP | BINARY_OP | VARIABLE_OP | NUMBER | EOF | TEMPSTRING | SPACE

datatype Token = Pair(token_type:TokenType, token_value:string)
datatype Result<T> = Ok(data: T) | Err(error: string)

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
    token.token_type==SPACE
}
predicate isWhiteSpace(ch: char){
    ch==' '
}
function Flatten(tok: seq<Token>): seq<char>
/*requires forall
ensures |Flatten(tok)|>|tok|
ensures |tok|>=1 ==> (tok[|tok|-1].token_value==Flatten(tok)[(|Flatten(tok)|)-(|tok[|tok|-1].token_value|)..(|Flatten(tok)|)]);
ensures forall i::0<=i<|tok| ==> exists j: nat::tok[i].token_value==Flatten(tok)[j..j+|tok[i].token_value|]*/{
    if |tok|==0 then []
    else Flatten(tok[0..|tok|-1])+tok[|tok|-1].token_value
    
  
}

ghost predicate contains(str: seq<char>, substr: seq<char>){
    exists i: nat:: exists l:nat :: (i+l<=|str| && substr==str[i..i+l])
}

/*lemma FlatContains(tok:seq<Token>){
    assert |tok|>0 ==> Flatten(tok)==Flatten(tok[0..|tok|-1])+tok[|tok|-1].token_value;
    assert exists i: nat:: exists l:nat :: (i+l<=|Flatten(tok)| && tok[|tok|-1].token_type==Flatten(tok)[i..i+l]) by {
        var i:=
        var l:=length()

    }
    ghost var i:=0;
    while (i<|tok|)
    //invariant forall j::0<=j<i ==>
    {

    }
}
*/
function Spaceless(str: seq<char>): seq<char>
{
    if |str|==0 then []
    else if isWhiteSpace(str[|str|-1]) then Spaceless(str[0..|str|-1])
    else Spaceless(str[0..|str|-1])+[str[|str|-1]]
}
lemma SpaceAdd(ch: char,str:seq<char>)
requires !isWhiteSpace(ch)
ensures Spaceless(str+[ch])==Spaceless(str)+[ch];
{

}
lemma SpaceAddTok(tokVal: seq<char>, str:seq<char>)
requires forall i::0<=i<|tokVal| ==> !isWhiteSpace(tokVal[i])
ensures Spaceless(str+tokVal)==Spaceless(str)+tokVal
{
    ghost var i:=0;
    assert str+tokVal[0..i]==str;
    assert Spaceless(str)+tokVal[0..i]==Spaceless(str);
    assert Spaceless(str+tokVal[0..i])==Spaceless(str);
    while i<|tokVal|
    invariant i<=|tokVal|
    invariant Spaceless(str)+tokVal[0..i]==Spaceless(str+tokVal[0..i])
    {
        assert !isWhiteSpace(tokVal[i]);
        ghost var a:=str+tokVal[0..i];
        //assert a==str+tokVal[0..i];
        SpaceAdd(tokVal[i],a);
        assert Spaceless(a)+[tokVal[i]]==Spaceless(a+[tokVal[i]]);
        //assert a==str+tokVal[0..i];
        assert a+[tokVal[i]]==str+tokVal[0..i+1];
        assert Spaceless(str)+tokVal[0..i+1]==Spaceless(str+tokVal[0..i+1]);
        i:=i+1;
    }
    assert tokVal[0..i]==tokVal;
}
lemma FlatAdd(tok:seq<Token>)
    requires |tok|>=1
    ensures Flatten(tok[0..|tok|])==Flatten(tok[0..|tok|-1])+tok[|tok|-1].token_value;
{
    assert tok==tok[0..|tok|];
    assert Flatten(tok)==Flatten(tok[0..|tok|]);
    assert Flatten(tok)==Flatten(tok[0..|tok|-1])+tok[|tok|-1].token_value;

}

lemma PartialFlatAdd(i: nat, tok:seq<Token>)
    requires |tok|>=1
    requires i<|tok|
    ensures Flatten(tok[0..i+1])==Flatten(tok[0..i])+tok[i].token_value
{
    ghost var a:=tok[0..i+1];
    FlatAdd(a);
    assert Flatten(a)==Flatten(a[0..|a|-1])+a[|a|-1].token_value;
    assert tok[0..i+1]==a;
    assert tok[0..i]==a[0..|a|-1];
}

lemma Flatsame(tok: seq<Token>,tok2: seq<Token>)
requires |tok|==|tok2|
requires forall i :: 0<=i<|tok| ==> tok[i].token_value==tok2[i].token_value;
ensures Flatten(tok)==Flatten(tok2)
{

}

lemma FlatInclude(i: nat, tok:seq<Token>,str:seq<char>)
requires Flatten(tok)==str
ensures exists j : nat:: tok[i].token_value==str[j..j+|tok[i].token_value|]
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
predicate ValidString(str: seq<char>){
    str=="abs" ||
    str=="sqrt" ||
    str=="ceil" ||
    str=="modulo" ||
    str=="expt" ||
    str=="min" ||
    str=="max"

}
predicate ValidNumber(tok: Token){
    forall i::0<=i<|tok.token_value| ==>(
        (tok.token_value[i] as int >=48 && tok.token_value[i] as int  <=57)
        || tok.token_value[i]=='.'
    )
}
predicate ValidWhiteSpace(tok: Token){
    tok.token_value==" " || tok.token_value=="\n" || tok.token_value=="\t"
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

method Lex1(str: seq<char>) returns (tokenized: Result<seq<Token>>)
/*requires forall i::0<=i<|str| ==> (
(str[i] as int >=48 && str[i] as int  <=57) ||
str[i]=='+' ||
str[i]=='-' ||
str[i]=='*' ||
str[i]=='/' ||
str[i]=='(' ||
str[i]==')'
)*/



ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> ((validtype(tokenized.data[i])) ||tokenized.data[i].token_type==TEMPSTRING)

//ensures all tokens are valid and correct type
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (
    validValue(tokenized.data[i])
)

//ensures all characters are represented in order in tokens
ensures tokenized.Ok? ==> Flatten(tokenized.data)==str;

//ensures no false positives when returning errors
ensures tokenized.Err? ==> (

(exists i: nat:: i<|str| && !(
    ((str[i] as int >=48 && str[i] as int  <=57) || str[i]=='.') ||
    (str[i] as int >=97 && str[i] as int  <=122) ||
    str[i]=='+' ||
    str[i]=='-' ||
    str[i]=='*' ||
    str[i]=='/' ||
    str[i]=='(' ||
    str[i]==')' ||
    (str[i]==' ' || str[i]=='\n' || str[i]=='\t')
)
)
)
/*||
(exists i: nat ::
!ValidString(tok[i].token_value) && forall j::0<=j<|tok[i].token_value| ==>(tok[i].token_value[j] as int >=97 && tok[i].token_value[j] as int  <=122)
)
*/


{
    var i:=0;
    //var tokpos:=0;
    var tok: seq<Token> := [];
    while i<|str|
    invariant forall i:: 0<=i<|tok| ==> (validType(tok[i]) ||tok[i].token_type==TEMPSTRING)
    invariant i<=|str|
    invariant forall i:: 0<=i<|tok| ==> (validValue(tok[i])||tok[i].token_type==TEMPSTRING)
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
            if(|tok|>=1 && tok[|tok|-1].token_type==TEMPSTRING){ //if last is letter
                tok := tok[|tok|-1 :=   //add letter
                Pair(TEMPSTRING,tok[|tok|-1].token_value+[str[i]])];
                assert(tok[|tok|-1].token_type==TEMPSTRING);
            }
            else{
                tok:=tok + [Pair(TEMPSTRING,[str[i]])];
                assert(tok[|tok|-1].token_type==TEMPSTRING);
            }
            assert(tok[|tok|-1].token_type==TEMPSTRING);
            //assert(str[i-|tok[|tok|-1].token_value|..i+1]==tok|))
        }
        //basic symbols
        else{
            if(str[i]=='+'){
                tok:=tok + [Pair(PLUS,"+")];
                //IDK WHY THIS LINE IN PARTICULAR HELPS THE PROVER, BUT IT DOES SO I'M KEEPING IT
                assert Flatten(tok)==str[0..i+1];
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
            else if(str[i]==' ' || str[i]=='\n' || str[i]=='\t'){
                tok:=tok + [Pair(SPACE,[str[i]])];
                assert ValidWhiteSpace(tok[|tok|-1]);
            }
            else{
                assert !(
                    ((str[i] as int >=48 && str[i] as int  <=57) || str[i]=='.') ||
                    (str[i] as int >=97 && str[i] as int  <=122) ||
                    str[i]=='+' ||
                    str[i]=='-' ||
                    str[i]=='*' ||
                    str[i]=='/' ||
                    str[i]=='(' ||
                    str[i]==')' ||
                    (str[i]==' ' || str[i]=='\n' || str[i]=='\t')
                );
                return Err("invalid string");
            }  
            //tokpos:=tokpos+1;
            //num==0;
        }
         
        assert validtype(tok[|tok|-1]) || tok[|tok|-1].token_type==TEMPSTRING;
        assert validValue(tok[|tok|-1]) || tok[|tok|-1].token_type==TEMPSTRING;
        i:=i+1;
        
        //assert forall i:: 0<=i<|tok| ==> validValue(tok[i]);
    }
    return Ok(tok);

}




method DefineTokens (oldtok: seq<Token>, str: seq<char>) returns (tokenized: Result<seq<Token>>)

//ensures no tempstrings
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (validtype(tokenized.data[i]))

//ensures all tokens are valid and correct type
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (
    validValue(tokenized.data[i])
)

//ensures all characters are represented in order in tokens
ensures tokenized.Ok? ==> Flatten(tokenized.data)==str;
requires forall i:: 0<=i<|oldtok| ==> (validtype(oldtok[i]) || oldtok[i].token_type==TEMPSTRING)
requires forall i:: 0<=i<|oldtok| ==> (validValue(oldtok[i]) || oldtok[i].token_type==TEMPSTRING)
requires Flatten(oldtok)==str;

ensures tokenized.Err? ==> (
    exists i:nat :: 
        (i<|oldtok| && oldtok[i].token_type==TEMPSTRING && !ValidString(oldtok[i].token_value))
)

{
    var tok:=oldtok;

    
    ghost var a:=tok;
    var i:=0;

    while i<|tok|
    invariant i<=|tok|
    invariant forall j:: 0<=j<i ==> validValue(tok[j])
    invariant forall j:: 0<=j<|tok| ==> (validtype(tok[j]) ||tok[j].token_type==TEMPSTRING);
    invariant forall j:: 0<=j<|tok| ==> (validValue(tok[j]) ||tok[j].token_type==TEMPSTRING);
    invariant forall j:: 0<=j<i ==> ((validtype(tok[j])))
    invariant |a|==|tok|
    invariant forall j:: i<=j<|tok| ==> tok[j].token_type==oldtok[j].token_type
    invariant forall j:: 0<=j<|tok| ==> a[j].token_value==tok[j].token_value
    invariant Flatten(tok)==str
    {
        //ghost var a:=tok[i];
        //assert validtype(tok[i]) || tok[i].token_type==TEMPSTRING;
        if(tok[i].token_type==TEMPSTRING){ //if token is string
            assert oldtok[i].token_type==TEMPSTRING;
            
            if(ValidUnary(tok[i])){
                tok := tok[i :=
                Pair(UNARY_OP,tok[i].token_value)];
                //assert validtype(tok[i]);
            }
            else if(ValidBinary(tok[i].token_value)){
                tok := tok[i :=
                Pair(BINARY_OP,tok[i].token_value)];
                //assert validtype(tok[i]);
            }
            else if(ValidVariable(tok[i].token_value)){
                tok := tok[i :=
                Pair(VARIABLE_OP,tok[i].token_value)];
                //assert validtype(tok[i]);
            }
            else{
                //assert i<|oldtok|;
                //assert oldtok[i].token_type==TEMPSTRING;
                assert (i<|oldtok| && oldtok[i].token_type==TEMPSTRING && !ValidString(oldtok[i].token_value));
                return Err("invalid string");
            }   
            //assert validtype(tok[i]);
        }
        assert a[i].token_value==tok[i].token_value;
        Flatsame(tok,a);
        assert tok[i].token_type!=TEMPSTRING;
        assert validtype(tok[i]);
        //assert tok[i].token_type==UNARY_OP ==> ValidUnary(tok[i]);
        i:=i+1;
    }
    return Ok(tok);
}

method RemoveSpaces(tok: seq<Token>) returns (spaceless: seq<Token>)
ensures forall i:: 0<=i<|spaceless| ==> spaceless[i].token_type!=SPACE
ensures Flatten(spaceless)==Spaceless(Flatten(tok))
{
    var i:=0;
    var out: seq<Token> := [];
    while i<|tok|
    invariant i<=|tok|
    invariant forall j::0<=j<|out| ==> out[j].token_type!=SPACE
    invariant Flatten(out)==Spaceless(Flatten(tok[0..i]))
    {
        //assume tok[i].token_type==SPACE;
        if tok[i].token_type!=SPACE{
            out:=out+[tok[i]];
            PartialFlatAdd(i,tok);
            //FlatAdd(tok[0..i+1]);
            assert Flatten(tok[0..i+1])==Flatten(tok[0..i])+tok[i].token_value;
            assume tok[i].token_value=="abc";
            SpaceAddTok(tok[i].token_value,Flatten(tok[0..i]));
            assert Spaceless(Flatten(tok[0..i+1]))==Spaceless(Flatten(tok[0..i]))+tok[i].token_value;
        }
        else{
            assume tok[i].token_value==" ";
            PartialFlatAdd(i,tok);
            //FlatAdd(tok[0..i+1]);
            assert Flatten(tok[0..i+1])==Flatten(tok[0..i])+tok[i].token_value;
            assert Spaceless(Flatten(tok[0..i+1]))==Spaceless(Flatten(tok[0..i]));
        }
        i:=i+1;
    }
    assert i==|tok|;
    assert tok[0..|tok|]==tok;
    return out;
}



/*match result_var
           case Ok => do something;
           case Err => do something else;*/
