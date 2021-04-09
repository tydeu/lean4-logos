import Gaea.Logic.Eq.Rules
import Gaea.Logic.Rel.Theorems

namespace Gaea.Logic

universes u v
variable {P : Sort u} 

class MEq (L : Logic P) (T : Sort v) extends LEq P T :=
  toEqRefl : Refl L toLEq.eq
  toEqPredSubst : PredSubst L toLEq.eq

variable {T : Sort v}

instance iMEq {L : Logic P} 
  [Q : LEq P T] [R : Refl L Q.eq] [P : PredSubst L Q.eq] : MEq L T 
  := {toLEq := Q, toEqRefl := R, toEqPredSubst := P}

namespace MEq
abbrev eq {L : Logic P} (K : MEq L T) 
  := K.toLEq.eq
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
  [K : MEq L T] : Refl L K.eq := {refl := K.refl}

instance iPredSubstOfMEq {L : Logic P}
  [K : MEq L T] : PredSubst L K.eq := {predSubst := K.predSubst}

namespace MEq
-- FunSubst
abbrev toEqFunSubst {L : Logic P} (K : MEq L T) 
  : FunSubst L K.eq := iFunSubstByReflPredSubst
abbrev toFunSubst {L : Logic P} (K : MEq L T)
  := K.toEqFunSubst
abbrev eqFunSubst {L : Logic P} (K : MEq L T) 
  := K.toEqFunSubst.funSubst
abbrev funSubst {L : Logic P} (K : MEq L T) 
  := K.eqFunSubst
-- Symm
abbrev toEqSymm {L : Logic P} (K : MEq L T) 
  : Symm L K.eq := iSymmByReflPredSubst
abbrev toSymm {L : Logic P} (K : MEq L T)
  := K.toEqSymm
abbrev eqSymm {L : Logic P} (K : MEq L T) 
  := K.toEqSymm.symm
abbrev symm {L : Logic P} (K : MEq L T) 
  := K.eqSymm
-- Trans
abbrev toEqTrans {L : Logic P} (K : MEq L T) 
  : Trans L K.eq := iTransByPredSubst
abbrev toTrans {L : Logic P} (K : MEq L T) 
  := K.toEqTrans
abbrev eqTrans {L : Logic P} (K : MEq L T) 
  := K.toEqTrans.trans
abbrev trans {L : Logic P} (K : MEq L T) 
  := K.eqTrans
-- LeftEuc
abbrev toEqLeftEuc {L : Logic P} (K : MEq L T) 
  : LeftEuc L K.eq := iLeftEucBySymmTrans
abbrev toLeftEuc {L : Logic P} (K : MEq L T)
  := K.toEqLeftEuc
abbrev eqLeftEuc {L : Logic P} (K : MEq L T) 
  := K.toEqLeftEuc.leftEuc
abbrev leftEuc {L : Logic P} (K : MEq L T) 
  := K.eqLeftEuc
-- RightEuc
abbrev toEqRightEuc {L : Logic P} (K : MEq L T) 
  : RightEuc L K.eq := iRightEucBySymmTrans
abbrev toRightEuc {L : Logic P} (K : MEq L T)
  := K.toEqRightEuc
abbrev eqRightEuc {L : Logic P} (K : MEq L T) 
  := K.toEqRightEuc.rightEuc
abbrev rightEuc {L : Logic P} (K : MEq L T) 
  := K.eqRightEuc
end MEq

end Gaea.Logic