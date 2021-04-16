import Gaea.Logic.Eq.Syntax
import Gaea.Logic.Rel.Theorems

namespace Gaea.Logic

universes u v
variable {P : Sort u} {T : Sort v}

--------------------------------------------------------------------------------
-- Partial Equality
--------------------------------------------------------------------------------

class PEq (L : Logic P) (T : Sort v) extends SEq P T :=
  Symm : Symm L toFun
  Trans : Trans L toFun

instance iPEq {L : Logic P} 
  [Q : SEq P T] [Sm : Symm L Q.toFun] [Tr : Trans L Q.toFun] : PEq L T 
  := {toSEq := Q, Symm := Sm, Trans := Tr}

instance iSymmOfPEq {L : Logic P} 
  [K : PEq L T] : Symm L K.toFun := K.Symm

instance iTransOfPEq {L : Logic P}
  [K : PEq L T] : Trans L K.toFun := K.Trans

namespace PEq

-- Symm
abbrev symm {L : Logic P} (K : PEq L T) 
  {a b} := K.Symm.symm a b

-- Trans
abbrev trans {L : Logic P} (K : PEq L T) 
  {a b c} := K.Trans.trans a b c

-- LeftEuc
abbrev LeftEuc {L : Logic P} (K : PEq L T) 
  : LeftEuc L K.toFun := iLeftEucBySymmTrans
abbrev leftEuc {L : Logic P} (K : PEq L T) 
  {a b c} := K.LeftEuc.leftEuc a b c

-- RightEuc
abbrev RightEuc {L : Logic P} (K : PEq L T) 
  : RightEuc L K.toFun := iRightEucBySymmTrans
abbrev rightEuc {L : Logic P} (K : PEq L T) 
  {a b c} := K.RightEuc.rightEuc a b c

end PEq 

--------------------------------------------------------------------------------
-- Relational Equality
--------------------------------------------------------------------------------

class REq (L : Logic P) (T : Sort v) extends PEq L T :=
  Refl : Refl L toFun

instance iREq {L : Logic P} [Q : SEq P T] 
  [Rf : Refl L Q.toFun]  [Sm : Symm L Q.toFun] [Tr : Trans L Q.toFun] : REq L T 
  := {toSEq := Q, Refl := Rf, Symm := Sm, Trans := Tr}

instance iReflOfREq {L : Logic P} 
  [K : REq L T] : Refl L K.toFun := K.Refl

namespace REq

-- Refl
abbrev refl {L : Logic P} (K : REq L T) 
  := K.Refl.refl

end REq

--------------------------------------------------------------------------------
-- Logical Equality
--------------------------------------------------------------------------------

class LEq (L : Logic P) (T : Sort v) extends REq L T :=
  PredSubst : PredSubst L toFun

instance iLEq {L : Logic P} 
  [Q : SEq P T] [R : Refl L Q.toFun] [P : PredSubst L Q.toFun] : LEq L T := 
  {toSEq := Q, PredSubst := P, Refl := R, 
    Symm := iSymmByReflPredSubst, Trans := iTransByPredSubst}

instance iPredSubstOfLEq {L : Logic P}
  [K : LEq L T] : PredSubst L K.toFun := K.PredSubst

namespace LEq

-- PredSubst
abbrev predSubst {L : Logic P} (K : LEq L T) 
  {F a b} := K.PredSubst.predSubst F a b

-- FunSubst
abbrev toFunSubst {L : Logic P} (K : LEq L T) 
  : FunSubst L K.toFun := iFunSubstByReflPredSubst
abbrev funSubst {L : Logic P} (K : LEq L T) 
  {f a b} := K.toFunSubst.funSubst f a b

end LEq

end Gaea.Logic