import Gaea.Logic.Dual.Rules
import Gaea.Logic.Prop.Tactics

namespace Gaea.Logic

-- Proofs

scoped macro "byContraposition " x:binderIdent : tactic => 
  `(tactic| apply byContraposition; intro $(x[0]))

scoped macro "byContradiction " x:binderPat : tactic => 
  `(tactic| apply byContradiction; assume $x)

scoped macro "contradiction " np:term:max p:term:max : tactic => 
  `(tactic| exact contradiction $np $p)

scoped macro "adFalso " x:binderPat : tactic => 
  `(tactic| apply adFalso; assume $x)

scoped macro "noncontradiction " np:term:max p:term:max : tactic => 
  `(tactic| exact noncontradiction $np $p)

-- Util

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
  `(tactic| apply dblNegElim (f := $(Lean.mkIdent `lneg)))
