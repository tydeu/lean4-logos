import Gaea.Logic.Unit.Rules
import Gaea.Logic.Prop.Tactics

namespace Gaea.Logic
-- Proofs

scoped syntax (name := conditionTactic) 
  "condition " (colGt binderPat)+ : tactic
macro_rules [conditionTactic]
  | `(tactic| condition $x:binderPat) => 
    `(tactic| apply condition; assume $x)
  | `(tactic| condition $x $y $zs*) => 
    `(tactic| condition $x; condition $y $zs*)

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

end Gaea.Logic