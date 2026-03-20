include "types.dfy"
include "validate.dfy"

//concatinates token values into a single string
function Flatten(tok: seq<Token>): seq<char>
{
    if |tok|==0 then []
    else Flatten(tok[0..|tok|-1])+tok[|tok|-1].token_value
}

//removes spaces from string
function Spaceless(str: seq<char>): seq<char>
{
    if |str|==0 then []
    else if isWhiteSpace(str[|str|-1]) then Spaceless(str[0..|str|-1])
    else Spaceless(str[0..|str|-1])+[str[|str|-1]]
}

//if non-whitespace character is added to str, Spaceless(str) appends that character
lemma SpaceAdd(ch: char,str:seq<char>)
requires !isWhiteSpace(ch)
ensures Spaceless(str+[ch])==Spaceless(str)+[ch]
{

}

//adding a non-whitespace token leads to Spaceless(str) appending that token value
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
        SpaceAdd(tokVal[i],a);
        assert Spaceless(a)+[tokVal[i]]==Spaceless(a+[tokVal[i]]);
        assert a+[tokVal[i]]==str+tokVal[0..i+1];
        assert Spaceless(str)+tokVal[0..i+1]==Spaceless(str+tokVal[0..i+1]);
        i:=i+1;
    }
    assert i==|tokVal|;
    assert tokVal[0..i]==tokVal;
}

//adding a token to a sequence adds the value to the Flattened result
lemma FlatAdd(tok:seq<Token>)
    requires |tok|>=1
    ensures Flatten(tok[0..|tok|])==Flatten(tok[0..|tok|-1])+tok[|tok|-1].token_value
{
    assert tok==tok[0..|tok|];
    assert Flatten(tok)==Flatten(tok[0..|tok|]);
    assert Flatten(tok)==Flatten(tok[0..|tok|-1])+tok[|tok|-1].token_value;
}

//same as FlatAdd but works with partial sequences
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

//if all token values are the same between two sequences, the Flattened return value is the same for both
lemma Flatsame(tok: seq<Token>,tok2: seq<Token>)
requires |tok|==|tok2|
requires forall i :: 0<=i<|tok| ==> tok[i].token_value==tok2[i].token_value
ensures Flatten(tok)==Flatten(tok2)
{

}

//if a valid token is not labeled as whitespace, it does not contain whitespace
lemma validLacksSpaces(tok:Token)
    requires validtype(tok)
    requires validValue(tok) && tok.token_type!=SPACE
    ensures (forall j::0<=j<|tok.token_value| ==> !isWhiteSpace(tok.token_value[j]))
{
    
}


//PHASE ONE OF LEXING: BREAKS STRING INTO SIMPLE TOKENS
method Lex1(str: seq<char>) returns (tokenized: Result<seq<Token>>)

//ensures all tokens are valid and correct type
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> ((validtype(tokenized.data[i])) ||tokenized.data[i].token_type==TEMPSTRING)
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (
    validValue(tokenized.data[i])
)

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

//ensures all characters are represented in order in tokens
ensures tokenized.Ok? ==> Flatten(tokenized.data)==str

{
    var i:=0;
    //var tokpos:=0;
    var tok: seq<Token> := [];
    while i<|str|
    invariant forall i:: 0<=i<|tok| ==> (validtype(tok[i]) ||tok[i].token_type==TEMPSTRING)
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
        }
        //basic symbols
        else{
            var c := str[i];
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
                return Err("bad character '" + [str[i]] + "'");
            }  
        }
         
        assert validtype(tok[|tok|-1]) || tok[|tok|-1].token_type==TEMPSTRING;
        assert validValue(tok[|tok|-1]);
        i:=i+1;
    }
    return Ok(tok);

}



//PHASE TWO OF LEXING: GIVES MORE SPECIFIC LABELS TO STRING TOKENS
method DefineTokens (oldtok: seq<Token>, str: seq<char>) returns (tokenized: Result<seq<Token>>)

//ensures no tempstrings
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (validtype(tokenized.data[i]))

//ensures all tokens are valid and correct type
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (
    validValue(tokenized.data[i])
)

//ensures all characters are represented in order in tokens
ensures tokenized.Ok? ==> Flatten(tokenized.data)==str

//requirements are same as ensures from Lex1 (should always be true)
requires forall i:: 0<=i<|oldtok| ==> (validtype(oldtok[i]) || oldtok[i].token_type==TEMPSTRING)
requires forall i:: 0<=i<|oldtok| ==> (validValue(oldtok[i]) || oldtok[i].token_type==TEMPSTRING)
requires Flatten(oldtok)==str

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
    invariant forall j:: 0<=j<|tok| ==> (validtype(tok[j]) ||tok[j].token_type==TEMPSTRING)
    invariant forall j:: 0<=j<|tok| ==> (validValue(tok[j]) ||tok[j].token_type==TEMPSTRING)
    invariant forall j:: 0<=j<i ==> ((validtype(tok[j])))
    invariant |a|==|tok|
    invariant forall j:: i<=j<|tok| ==> tok[j].token_type==oldtok[j].token_type
    invariant forall j:: 0<=j<|tok| ==> a[j].token_value==tok[j].token_value
    invariant Flatten(tok)==str
    {
        if(tok[i].token_type==TEMPSTRING){ //if token is string
            assert oldtok[i].token_type==TEMPSTRING;
            
            if(ValidUnary(tok[i].token_value)){
                tok := tok[i :=
                Pair(UNARY_OP,tok[i].token_value)];
            }
            else if(ValidBinary(tok[i].token_value)){
                tok := tok[i :=
                Pair(BINARY_OP,tok[i].token_value)];
            }
            else if(ValidVariable(tok[i].token_value)){
                tok := tok[i :=
                Pair(VARIABLE_OP,tok[i].token_value)];
            }
            else{
                assert (i<|oldtok| && oldtok[i].token_type==TEMPSTRING && !ValidString(oldtok[i].token_value));
                return Err("invalid string");
            }   
        }
        assert a[i].token_value==tok[i].token_value;
        Flatsame(tok,a);
        assert tok[i].token_type!=TEMPSTRING;
        assert validtype(tok[i]);
        i:=i+1;
    }
    return Ok(tok);
}


//PHASE THREE OF LEXING: REMOVES WHITESPACE TOKENS
method RemoveSpaces(tok: seq<Token>) returns (spaceless: Result<seq<Token>>)

//requires are same as ensures from DefineTokens (should always be true)
requires forall i:: 0<=i<|tok| ==> (validValue(tok[i]))
requires forall i:: 0<=i<|tok| ==> (validtype(tok[i]))

//should never throw error
ensures spaceless.Ok?

//tokens should be valid type/value
ensures forall i:: 0<=i<|spaceless.data| ==> (validValue(spaceless.data[i]))
ensures forall i:: 0<=i<|spaceless.data| ==> (validtype(spaceless.data[i]))

//whitespaces should be gone
ensures forall i:: 0<=i<|spaceless.data| ==> spaceless.data[i].token_type!=SPACE

//tokens should be representative of original string (without spaces)
ensures Flatten(spaceless.data)==Spaceless(Flatten(tok))

{
    var i:=0;
    var out: seq<Token> := [];
    
    while i<|tok|
    invariant i<=|tok|
    invariant forall i:: 0<=i<|tok| ==> (validValue(tok[i]))
    invariant forall i:: 0<=i<|tok| ==> (validtype(tok[i]))
    invariant forall j::0<=j<|out| ==> (out[j].token_type!=SPACE && validValue(out[j]) && validtype(out[j]))
    invariant Flatten(out)==Spaceless(Flatten(tok[0..i]))
    {
        if tok[i].token_type!=SPACE{
            validLacksSpaces(tok[i]);
            assert (forall j::0<=j<|tok[i].token_value| ==> !isWhiteSpace(tok[i].token_value[j]));
            out:=out+[tok[i]];
            PartialFlatAdd(i,tok);
            assert Flatten(tok[0..i+1])==Flatten(tok[0..i])+tok[i].token_value;
            SpaceAddTok(tok[i].token_value,Flatten(tok[0..i]));
            assert Spaceless(Flatten(tok[0..i+1]))==Spaceless(Flatten(tok[0..i]))+tok[i].token_value;
        }
        else{
            assert tok[i].token_value==" " || tok[i].token_value=="\n" || tok[i].token_value=="\t";
            assert |tok[i].token_value|==1;
            assert isWhiteSpace(tok[i].token_value[0]);
            PartialFlatAdd(i,tok);
            assert Flatten(tok[0..i+1])==Flatten(tok[0..i])+tok[i].token_value;
            assert Spaceless(Flatten(tok[0..i+1]))==Spaceless(Flatten(tok[0..i]));
        }
        i:=i+1;
    }
    assert i==|tok|;
    assert tok[0..|tok|]==tok;
    return Ok(out);
}


//OVERALL LEXING METHOD: TAKES STRING AND CONVERTS INTO USEFUL TOKENS FOR PARSING
method lex (str:seq<char>)returns (tokenized: Result<seq<Token>>)
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> ((validtype(tokenized.data[i])))

//ensures all tokens are valid and correct type
ensures tokenized.Ok? ==> forall i:: 0<=i<|tokenized.data| ==> (
    validValue(tokenized.data[i])
)

//ensures all characters are represented in order in tokens

ensures tokenized.Ok ==> ensures Flatten(tokenized)==Spaceless(Flatten(str))

{
    var tok:= Lex1(str);
    if(tok.Ok?){
        tok:=DefineTokens(tok.data,str);
        if(tok.Ok?){
            tok:=RemoveSpaces(tok.data);
            return tok;
        }
        return tok;
    }
    return tok;


}
