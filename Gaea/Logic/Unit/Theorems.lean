import Gaea.Logic.Fun.Rules
import Gaea.Logic.Unit.Rules
import Gaea.Logic.Unit.Tactics
import Gaea.Logic.Rel.Rules

universe u
variable {P : Sort u}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Entailment
--------------------------------------------------------------------------------

-- Transitivity
-- (|- p -> q) -> (|- q -> r) -> (|- p -> r)

def transByCondMp {L : Logic P} 
{F : Binar P} (C : Condition L F) (Mp : ModusPonens L F)
: (p q r : P) -> (L |- F p q) -> (L |- F q r) -> (L |- F p r)
:= by
  intro p q r 
  assume LpTq LqTr
  condition Lp
  mp LqTr (mp LpTq Lp) 

instance iTransByCondMp {L : Logic P} 
{F : Binar P} [C : Condition L F] [Mp : ModusPonens L F]
: Trans L F := {toFun := transByCondMp C Mp}

end Gaea.Logic
