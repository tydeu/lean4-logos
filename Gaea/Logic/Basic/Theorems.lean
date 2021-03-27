import Gaea.Logic.Rules
import Gaea.Logic.Basic.Rules
import Gaea.Logic.Basic.Modules
import Gaea.Logic.Rel.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}

--------------------------------------------------------------------------------
-- If
--------------------------------------------------------------------------------

-- Reflexitivity
-- p -> (p -> p)

def ifReflByIIntro {L : Logic P} 
{If : LIf P} (IfI : IfIntro L If)
: (p : P) -> (L |- p -> p)
:= by
  intro p
  apply ifIntro
  exact id 

instance iIfReflByIntro {L : Logic P} [If : LIf P] [IfI : IfIntro L If]
: LRefl L If.lIf := {lRefl := ifReflByIIntro IfI}

namespace MIf
abbrev toLRefl {L : Logic P} (K : MIf L) : LRefl L K.lIf := iIfReflByIntro
abbrev toRefl {L : Logic P} (K : MIf L) : Refl L K.lIf := iReflOfLRefl
abbrev ifRefl {L : Logic P} (K : MIf L) := K.toLRefl.lRefl
abbrev refl {L : Logic P} (K : MIf L) := K.ifRefl
abbrev toTaut {L : Logic P} (K : MIf L) : Taut L K.lIf := iTautOfLRefl
abbrev ifTaut {L : Logic P} (K : MIf L) := K.toTaut.taut
abbrev taut {L : Logic P} (K : MIf L) {p} := K.ifTaut p
end MIf

-- Transitivity
-- (p -> q) -> (q -> r) -> (p -> r)

def ifTransByIE {L : Logic P} 
{If : LIf P} (IfI : IfIntro L If) (IfE : IfElim L If)
: (p q r : P) -> (L |- p -> q) -> (L |- q -> r) -> (L |- p -> r)
:= by
  intro p q r LpTq LqTr
  apply ifIntro; intro Lp
  exact ifElim LqTr (ifElim LpTq Lp) 

instance iIfTransByIE {L : Logic P} 
[If : LIf P] [IfI : IfIntro L If] [IfE : IfElim L If]
: LTrans L If.lIf := {lTrans := ifTransByIE IfI IfE}

namespace MIf
abbrev toLTrans {L : Logic P} (K : MIf L) : LTrans L K.lIf := iIfTransByIE
abbrev toTrans {L : Logic P} (K : MIf L) : Trans L K.lIf := iTransOfLTrans
abbrev ifTrans {L : Logic P} (K : MIf L) := K.toLTrans.lTrans
abbrev trans {L : Logic P} (K : MIf L) {p q r} := K.ifTrans p q r
end MIf

end Gaea.Logic