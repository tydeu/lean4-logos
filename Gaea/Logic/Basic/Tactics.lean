import Gaea.Logic.Basic.Rules

namespace Gaea.Logic

syntax binderIdent := ident <|> "_"

scoped syntax (name := uncurry) "uncurry " (colGt binderIdent)* : tactic
macro_rules [uncurry]
  | `(tactic| uncurry) => 
    `(tactic| apply conjUncurry)
  | `(tactic| uncurry $x) => 
    `(tactic| apply conjUncurry; intro $(x[0]))
  | `(tactic| uncurry $x $y $ys*) => 
    `(tactic| uncurry $x; uncurry $y $ys*)

syntax parenBinderIdents := "(" binderIdent,+ ")"
syntax braktBinderIdents := "[" binderIdent,+ "]"

scoped syntax (name := assume) "assume " 
    (colGt (binderIdent <|> parenBinderIdents <|> braktBinderIdents))+ : tactic
macro_rules [assume]
  | `(tactic| assume $x:binderIdent) => 
    `(tactic| intro $(x[0]))
  | `(tactic| assume ($x:binderIdent)) => 
    `(tactic| intro $(x[0]))
  | `(tactic| assume ($x:binderIdent, $ys,*)) => 
    `(tactic| uncurry $x; assume ($ys,*))
  | `(tactic| assume [$xs,*]) => 
    `(tactic| apply ifIntro; assume ($xs,*))
  | `(tactic| assume $x $y $zs*) => 
    `(tactic| assume $x; assume $y $zs*)

scoped macro "byContradiction " x:binderIdent : tactic => 
  `(tactic| apply byContradiction; intro $(x[0]))

scoped macro "contradiction " p:term:max np:term:max : tactic => 
  `(tactic| exact contradiction $p $np)

end Gaea.Logic