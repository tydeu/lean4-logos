import Gaea.Logic.Eq.Rules
import Gaea.Logic.Rel.Theorems

namespace Gaea.Logic

universes u v
variable {P : Sort u} 

class MEq (L : Logic P) (T : Sort v) extends LEq P T :=
  toEqRefl : Refl L toLEq.lEq
  toEqPredSubst : PredSubst L toLEq.lEq

variable {T : Sort v}

instance iMEq {L : Logic P} 
  [Q : LEq P T] [R : Refl L Q.lEq] [P : PredSubst L Q.lEq] : MEq L T 
  := {toLEq := Q, toEqRefl := R, toEqPredSubst := P}

namespace MEq
abbrev lEq {L : Logic P} (K : MEq L T) 
  := K.toLEq.lEq
abbrev eq {L : Logic P} (K : MEq L T) 
  := K.lEq
abbrev toPredSubst {L : Logic P} (K : MEq L T)
  := K.toEqPredSubst
abbrev eqPredSubst {L : Logic P} (K : MEq L T) 
  := K.toEqPredSubst.predSubst
abbrev predSubst {L : Logic P} (K : MEq L T) 
  := K.eqPredSubst
abbrev toRefl {L : Logic P} (K : MEq L T)
  := K.toEqRefl
abbrev eqRefl {L : Logic P} (K : MEq L T) 
  := K.toEqRefl.refl
abbrev refl {L : Logic P} (K : MEq L T) 
  := K.eqRefl
end MEq

instance iReflOfMEq {L : Logic P} 
  [K : MEq L T] : Refl L K.lEq := {refl := K.refl}

instance iPredSubstOfMEq {L : Logic P}
  [K : MEq L T] : PredSubst L K.lEq := {predSubst := K.predSubst}

namespace MEq
-- FunSubst
abbrev toEqFunSubst {L : Logic P} (K : MEq L T) 
  : FunSubst L K.lEq := iFunSubstByReflPredSubst
abbrev toFunSubst {L : Logic P} (K : MEq L T)
  := K.toEqFunSubst
abbrev eqFunSubst {L : Logic P} (K : MEq L T) 
  := K.toEqFunSubst.funSubst
abbrev funSubst {L : Logic P} (K : MEq L T) 
  := K.eqFunSubst
-- Symm
abbrev toEqSymm {L : Logic P} (K : MEq L T) 
  : Symm L K.lEq := iSymmByReflPredSubst
abbrev toSymm {L : Logic P} (K : MEq L T)
  := K.toEqSymm
abbrev eqSymm {L : Logic P} (K : MEq L T) 
  := K.toEqSymm.symm
abbrev symm {L : Logic P} (K : MEq L T) 
  := K.eqSymm
-- Trans
abbrev toEqTrans {L : Logic P} (K : MEq L T) 
  : Trans L K.lEq := iTransByPredSubst
abbrev toTrans {L : Logic P} (K : MEq L T) 
  := K.toEqTrans
abbrev eqTrans {L : Logic P} (K : MEq L T) 
  := K.toEqTrans.trans
abbrev trans {L : Logic P} (K : MEq L T) 
  := K.eqTrans
-- LeftEuc
abbrev toEqLeftEuc {L : Logic P} (K : MEq L T) 
  : LeftEuc L K.lEq := iLeftEucBySymmTrans
abbrev toLeftEuc {L : Logic P} (K : MEq L T)
  := K.toEqLeftEuc
abbrev eqLeftEuc {L : Logic P} (K : MEq L T) 
  := K.toEqLeftEuc.leftEuc
abbrev leftEuc {L : Logic P} (K : MEq L T) 
  := K.eqLeftEuc
-- RightEuc
abbrev toEqRightEuc {L : Logic P} (K : MEq L T) 
  : RightEuc L K.lEq := iRightEucBySymmTrans
abbrev toRightEuc {L : Logic P} (K : MEq L T)
  := K.toEqRightEuc
abbrev eqRightEuc {L : Logic P} (K : MEq L T) 
  := K.toEqRightEuc.rightEuc
abbrev rightEuc {L : Logic P} (K : MEq L T) 
  := K.eqRightEuc
end MEq

end Gaea.Logic