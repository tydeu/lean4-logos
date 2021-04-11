import Gaea.Logic.Prop.Rules

namespace Gaea.Logic

syntax binderIdent := ident <|> "_"

-- Proofs

scoped syntax (name := byImplicationTactic) 
  "byImplication " (colGt binderIdent)* : tactic
macro_rules [byImplicationTactic]
  | `(tactic| byImplication $x:binderIdent) => 
    `(tactic| apply byImplication; intro $(x[0]))
  | `(tactic| byImplication $x $y $zs*) => 
    `(tactic| byImplication $x; byImplication $y $zs*)

scoped macro "mp " pTq:term:max p:term:max : tactic => 
  `(tactic| exact mp $pTq $p)

scoped macro "byContraposition " x:binderIdent : tactic => 
  `(tactic| apply byContraposition; intro $(x[0]))

scoped macro "mt " pTq:term:max np:term:max : tactic => 
  `(tactic| exact mt $pTq $np)

scoped macro "dblNegElim" : tactic => 
  `(tactic| apply dblNegElim (lnot := $(Lean.mkIdent `lnot)))

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
    `(tactic| apply byImplication; assume ($xs,*))
  | `(tactic| assume $x $y $zs*) => 
    `(tactic| assume $x; assume $y $zs*)

end Gaea.Logic