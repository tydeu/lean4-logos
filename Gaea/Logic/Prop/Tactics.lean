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

scoped macro "mp " pq:term:max p:term:max : tactic => 
  `(tactic| exact mp $pq $p)

scoped macro "mpr " pq:term:max q:term:max : tactic => 
  `(tactic| exact mpr $pq $q)

scoped macro "leftMp " pq:term:max p:term:max : tactic => 
  `(tactic| exact leftMp $pq $p)

scoped macro "rightMp " pq:term:max p:term:max : tactic => 
  `(tactic| exact rightMp $pq $p)

scoped macro "mt " pq:term:max np:term:max : tactic => 
  `(tactic| exact mt $pq $np)

scoped macro "mtr " pq:term:max nq:term:max : tactic => 
  `(tactic| exact mtr $pq $nq)

scoped macro "leftMt " pq:term:max np:term:max : tactic => 
  `(tactic| exact leftMt $pq $np)

scoped macro "rightMt " pq:term:max nq:term:max : tactic => 
  `(tactic| exact rightMt $pq $nq)

scoped macro "mtp " pq:term:max np:term:max : tactic => 
  `(tactic| exact mtp $pq $np)

scoped macro "mtpr " pq:term:max nq:term:max : tactic => 
  `(tactic| exact mtpr $pq $nq)

scoped macro "leftMtp " pq:term:max np:term:max : tactic => 
  `(tactic| exact leftMtrp $pq $np)

scoped macro "rightMtp " pq:term:max nq:term:max : tactic => 
  `(tactic| exact rightMtp $pq $nq)

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