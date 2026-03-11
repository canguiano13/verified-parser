
class Expression {
  var value: int
  var left: Expression?
  var right: Expression?
}
class Token{
    var str: string
    var depth: int
    var precedence: int
}


method AssignDepths(tokens: array<Token>)
modifies tokens;
ensures tokens[0].depth==0

ensures forall i :: 1 <= i < tokens.Length ==>
(tokens[i-1].str=="(" ==> tokens[i].depth==tokens[i-1].depth+1)

ensures forall i :: 0 <= i < tokens.Length-1 ==>
(tokens[i].str==")" ==> tokens[i].depth==tokens[i+1].depth+1)

ensures forall i :: 0 <= i < tokens.Length-1 ==>
(tokens[i].str!="(" && tokens[i+1].str!=")" ==> tokens[i].depth==tokens[i+1].depth)
{

}
/*method AssignPrecedence(tokens: array<Token>) returns (idx: int)
modifies tokens

ensures()
{
    
}*/
method FindOperator(tokens: array<Token>) returns (idx: int)
ensures tokens[idx].str=="+" || tokens[idx].str=="-" || tokens[idx].str=="*" || tokens[idx].str=="/"
ensures forall i :: 0 <= i <tokens.Length ==> tokens[i].depth>tokens[idx].depth ||
(tokens[i].depth==tokens[idx].depth && tokens[i].precedence>tokens[idx].precedence) ||
(tokens[i].depth==tokens[idx].depth && tokens[i].precedence==tokens[idx].precedence && i<=idx)
{
    
}
