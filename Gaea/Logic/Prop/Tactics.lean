import Gaea.Logic.Prop.Rules

namespace Gaea.Logic

syntax binderIdent := ident <|> "_"

-- Prop Binding

declare_syntax_cat binderPat
syntax binderIdent : binderPat
syntax "(" binderPat,+ ")" : binderPat

scoped syntax (name := assume) 
  "assume " (colGt binderPat)+ : tactic
macro_rules [assume]
  | `(tactic| assume $x:binderIdent) => 
    `(tactic| intro $(x[0]))
  | `(tactic| assume ($x)) => 
    `(tactic| assume $x)
  | `(tactic| assume ($x, $ys,*)) => 
    `(tactic| apply uncurry; assume $x; assume ($ys,*))
  | `(tactic| assume $x $y $zs*) => 
    `(tactic| assume $x; assume $y $zs*)

-- Proofs

scoped syntax (name := byImplicationTactic) 
  "byImplication " (colGt binderPat)+ : tactic
macro_rules [byImplicationTactic]
  | `(tactic| byImplication $x:binderPat) => 
    `(tactic| apply byImplication; assume $x)
  | `(tactic| byImplication $x $y $zs*) => 
    `(tactic| byImplication $x; byImplication $y $zs*)

scoped macro "byContraposition " x:binderIdent : tactic => 
  `(tactic| apply byContraposition; intro $(x[0]))

scoped macro "byEither " pDq:term:max p:term:max q:term:max : tactic => 
  `(tactic| apply byEither $pDq $p $q)

scoped macro "byContradiction " x:binderPat : tactic => 
  `(tactic| apply byContradiction; assume $x)

scoped macro "contradiction " np:term:max p:term:max : tactic => 
  `(tactic| exact contradiction $np $p)

scoped macro "adFalso " x:binderPat : tactic => 
  `(tactic| apply adFalso; assume $x)

scoped macro "noncontradiction " np:term:max p:term:max : tactic => 
  `(tactic| exact noncontradiction $np $p)

-- Util

scoped macro "mp " pTq:term:max p:term:max : tactic => 
  `(tactic| exact mp $pTq $p)

scoped macro "mpl " pTq:term:max p:term:max : tactic => 
  `(tactic| exact mpl $pTq $p)

scoped macro "mpr " pTq:term:max p:term:max : tactic => 
  `(tactic| exact mpr $pTq $p)

scoped macro "mt " pTq:term:max np:term:max : tactic => 
  `(tactic| exact mt $pTq $np)

scoped macro "mtl " pTq:term:max np:term:max : tactic => 
  `(tactic| exact mtl $pTq $np)

scoped macro "mtr " pTq:term:max np:term:max : tactic => 
  `(tactic| exact mtr $pTq $np)

scoped macro "dblNegElim" : tactic => 
  `(tactic| apply dblNegElim (lnot := $(Lean.mkIdent `lnot)))

scoped syntax (name := uncurryTactic) 
  "uncurry " (colGt binderPat)* : tactic
macro_rules [uncurryTactic]
  | `(tactic| uncurry) => 
    `(tactic| apply uncurry)
  | `(tactic| uncurry $x) => 
    `(tactic| apply uncurry; assume $x)
  | `(tactic| uncurry $x $y $ys*) => 
    `(tactic| uncurry $x; uncurry $y $ys*)

end Gaea.Logic