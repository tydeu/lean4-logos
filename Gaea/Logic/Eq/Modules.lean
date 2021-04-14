import Gaea.Logic.Eq.Rules
import Gaea.Logic.Rel.Theorems

namespace Gaea.Logic

universes u v
variable {P : Sort u} {T : Sort v}

--------------------------------------------------------------------------------
-- Partial Equality
--------------------------------------------------------------------------------

class PEq (L : Logic P) (T : Sort v) extends SEq P T :=
  toEqSymm : Symm L eq
  toEqTrans : Trans L eq

instance iPEq {L : Logic P} 
  [Q : SEq P T] [Sm : Symm L Q.eq] [Tr : Trans L Q.eq] : PEq L T 
  := {toSEq := Q, toEqSymm := Sm, toEqTrans := Tr}

instance iSymmOfPEq {L : Logic P} 
  [K : PEq L T] : Symm L K.eq := K.toEqSymm

instance iTransOfPEq {L : Logic P}
  [K : PEq L T] : Trans L K.eq := K.toEqTrans

namespace PEq

-- Symm
abbrev toSymm {L : Logic P} (K : PEq L T)
  := K.toEqSymm
abbrev eqSymm {L : Logic P} (K : PEq L T) 
  := K.toEqSymm.symm
abbrev symm {L : Logic P} (K : PEq L T) 
  {a b} := K.eqSymm a b

-- Trans
abbrev toTrans {L : Logic P} (K : PEq L T) 
  := K.toEqTrans
abbrev eqTrans {L : Logic P} (K : PEq L T) 
  := K.toEqTrans.trans
abbrev trans {L : Logic P} (K : PEq L T) 
  {a b c} := K.eqTrans a b c

-- LeftEuc
abbrev toEqLeftEuc {L : Logic P} (K : PEq L T) 
  : LeftEuc L K.eq := iLeftEucBySymmTrans
abbrev toLeftEuc {L : Logic P} (K : PEq L T)
  := K.toEqLeftEuc
abbrev eqLeftEuc {L : Logic P} (K : PEq L T) 
  := K.toEqLeftEuc.leftEuc
abbrev leftEuc {L : Logic P} (K : PEq L T) 
  {a b c} := K.eqLeftEuc a b c

-- RightEuc
abbrev toEqRightEuc {L : Logic P} (K : PEq L T) 
  : RightEuc L K.eq := iRightEucBySymmTrans
abbrev toRightEuc {L : Logic P} (K : PEq L T)
  := K.toEqRightEuc
abbrev eqRightEuc {L : Logic P} (K : PEq L T) 
  := K.toEqRightEuc.rightEuc
abbrev rightEuc {L : Logic P} (K : PEq L T) 
  {a b c} := K.eqRightEuc a b c

end PEq 

--------------------------------------------------------------------------------
-- Relational Equality
--------------------------------------------------------------------------------

class REq (L : Logic P) (T : Sort v) extends PEq L T :=
  toEqRefl : Refl L eq

instance iREq {L : Logic P} 
  [Q : SEq P T] [Rf : Refl L Q.eq]  [Sm : Symm L Q.eq] [Tr : Trans L Q.eq] : REq L T 
  := {toSEq := Q, toEqRefl := Rf, toEqSymm := Sm, toEqTrans := Tr}

instance iReflOfREq {L : Logic P} 
  [K : REq L T] : Refl L K.eq := K.toEqRefl

namespace REq

-- Refl 
abbrev toRefl {L : Logic P} (K : REq L T)
  := K.toEqRefl
abbrev eqRefl {L : Logic P} (K : REq L T) 
  := K.toEqRefl.refl
abbrev refl {L : Logic P} (K : REq L T) 
  := K.eqRefl

end REq

--------------------------------------------------------------------------------
-- Logical Equality
--------------------------------------------------------------------------------

class LEq (L : Logic P) (T : Sort v) extends REq L T :=
  toEqPredSubst : PredSubst L eq

instance iLEq {L : Logic P} 
  [Q : SEq P T] [R : Refl L Q.eq] [P : PredSubst L Q.eq] : LEq L T := 
  {toSEq := Q, toEqPredSubst := P, toEqRefl := R, 
    toEqSymm := iSymmByReflPredSubst, toEqTrans := iTransByPredSubst}

instance iPredSubstOfLEq {L : Logic P}
  [K : LEq L T] : PredSubst L K.eq := K.toEqPredSubst

namespace LEq

-- PredSubst
abbrev toPredSubst {L : Logic P} (K : LEq L T)
  := K.toEqPredSubst
abbrev eqPredSubst {L : Logic P} (K : LEq L T) 
  := K.toEqPredSubst.predSubst
abbrev predSubst {L : Logic P} (K : LEq L T) 
  {F a b} := K.eqPredSubst F a b

-- FunSubst
abbrev toEqFunSubst {L : Logic P} (K : LEq L T) 
  : FunSubst L K.eq := iFunSubstByReflPredSubst
abbrev toFunSubst {L : Logic P} (K : LEq L T)
  := K.toEqFunSubst
abbrev eqFunSubst {L : Logic P} (K : LEq L T) 
  := K.toEqFunSubst.funSubst
abbrev funSubst {L : Logic P} (K : LEq L T) 
  {f a b} := K.eqFunSubst f a b

end LEq

end Gaea.Logic