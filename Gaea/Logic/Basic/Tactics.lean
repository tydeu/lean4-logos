import Gaea.Logic.Basic.Rules

namespace Gaea.Logic

syntax binderIdent := ident <|> "_"

-- Proofs

scoped syntax (name := byAssumptionTactic) 
  "byAssumption " (colGt binderIdent)* : tactic
macro_rules [byAssumptionTactic]
  | `(tactic| byAssumption $x:binderIdent) => 
    `(tactic| apply byAssumption; intro $(x[0]))
  | `(tactic| byAssumption $x $y $zs*) => 
    `(tactic| byAssumption $x; byAssumption $y $zs*)

scoped macro "mp " pTq:term:max p:term:max : tactic => 
  `(tactic| exact mp $pTq $p)

scoped macro "byContraposition " x:binderIdent : tactic => 
  `(tactic| apply byContraposition; intro $(x[0]))

scoped macro "mt " pTq:term:max np:term:max : tactic => 
  `(tactic| exact mt $pTq $np)

scoped macro "byContradiction " x:binderIdent : tactic => 
  `(tactic| apply byContradiction; intro $(x[0]))

scoped macro "contradiction " p:term:max np:term:max : tactic => 
  `(tactic| exact contradiction $p $np)

-- Util

scoped syntax (name := uncurryTactic) "uncurry " (colGt binderIdent)* : tactic
macro_rules [uncurryTactic]
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
    `(tactic| apply byAssumption; assume ($xs,*))
  | `(tactic| assume $x $y $zs*) => 
    `(tactic| assume $x; assume $y $zs*)

end Gaea.Logic