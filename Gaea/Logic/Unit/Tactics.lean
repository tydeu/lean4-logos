import Gaea.Logic.Unit.Rules
import Gaea.Logic.Prop.Tactics

namespace Gaea.Tactics

-- Proofs

scoped syntax (name := conditionTactic) 
  "condition " (colGt binderPat)+ : tactic
macro_rules (kind := conditionTactic)
  | `(tactic| condition $x:binderPat) => 
    `(tactic| apply condition; assume $x)
  | `(tactic| condition $x $y $zs*) => 
    `(tactic| condition $x; condition $y $zs*)

scoped syntax (name := leftCondTactic) 
  "leftCond " (colGt binderPat)+ : tactic
macro_rules (kind := leftCondTactic)
  | `(tactic| leftCond $x:binderPat) => 
    `(tactic| apply leftCond; assume $x)
  | `(tactic| leftCond $x $y $zs*) => 
    `(tactic| leftCond $x; leftCond $y $zs*)

scoped syntax (name := rightCondTactic) 
  "rightCond " (colGt binderPat)+ : tactic
macro_rules (kind := rightCondTactic)
  | `(tactic| rightCond $x:binderPat) => 
    `(tactic| apply rightCond; assume $x)
  | `(tactic| rightCond $x $y $zs*) => 
    `(tactic| rightCond $x; rightCond $y $zs*)

scoped macro "byEither " pq:term:max pr:term:max qr:term:max : tactic => 
  `(tactic| apply byEither $pq $pr $qr)

-- Util

scoped macro "mp " pq:term:max p:term:max : tactic => 
  `(tactic| exact mp $pq $p)

scoped macro "mpr " pq:term:max q:term:max : tactic => 
  `(tactic| exact mpr $pq $q)

scoped macro "leftMp " pq:term:max p:term:max : tactic => 
  `(tactic| exact leftMp $pq $p)

scoped macro "rightMp " pq:term:max p:term:max : tactic => 
  `(tactic| exact rightMp $pq $p)
