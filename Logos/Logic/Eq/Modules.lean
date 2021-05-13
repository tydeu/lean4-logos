import Logos.Logic.Eq.Syntax
import Logos.Logic.Rel.Theorems

universes u v
variable {P : Sort u} {T : Sort v}

namespace Logos

variable {L : Logic P}

--------------------------------------------------------------------------------
-- Partial Equality
--------------------------------------------------------------------------------

class PEq (L : Logic P) (T : Sort v) extends SEq P T :=
  Symm : Symm L eq
  Trans : Trans L eq

instance iPEq {L : Logic P} [Q : SEq P T] 
  [Sm : Symm L Q.toFun] [Tr : Trans L Q.toFun] : PEq L T := 
  {toSEq := Q, Symm := Sm, Trans := Tr}

namespace PEq

instance [K : PEq L T] 
  : Logos.Symm L K.toFun := K.Symm
instance [K : PEq L T] 
  : Logos.Trans L K.toFun := K.Trans

-- Symm
abbrev symm {L : Logic P} (K : PEq L T) 
  {a b} := K.Symm.toFun a b

-- Trans
abbrev trans {L : Logic P} (K : PEq L T) 
  {a b c} := K.Trans.toFun a b c

-- LeftEuc
abbrev LeftEuc {L : Logic P} (K : PEq L T) 
  : LeftEuc L K.toFun := iLeftEucBySymmTrans
abbrev leftEuc {L : Logic P} (K : PEq L T) 
  {a b c} := K.LeftEuc.toFun a b c

-- RightEuc
abbrev RightEuc {L : Logic P} (K : PEq L T) 
  : RightEuc L K.toFun := iRightEucBySymmTrans
abbrev rightEuc {L : Logic P} (K : PEq L T) 
  {a b c} := K.RightEuc.toFun a b c

end PEq 

--------------------------------------------------------------------------------
-- Relational Equality
--------------------------------------------------------------------------------

class REq (L : Logic P) (T : Sort v) extends PEq L T :=
  Refl : Refl L eq

instance iREq {L : Logic P} [Q : SEq P T] 
  [R : Refl L Q.toFun] [Sm : Symm L Q.toFun] [Tr : Trans L Q.toFun] : REq L T := 
  {toSEq := Q, Refl := R, Symm := Sm, Trans := Tr}

namespace REq

instance [K : REq L T] 
  : Logos.Refl L K.toFun := K.Refl

-- Refl
abbrev refl (K : REq L T) 
  := K.Refl.toFun

end REq

--------------------------------------------------------------------------------
-- Logical Equality
--------------------------------------------------------------------------------

class LEq (L : Logic P) (T : Sort v) extends REq L T :=
  PredSubst : PredSubst L eq
  Symm := iSymmByReflPredSubst
  Trans := iTransByPredSubst

instance iLEq {L : Logic P} [Q : SEq P T] 
  [R : Refl L Q.toFun] [Ps : PredSubst L Q.toFun] : LEq L T := 
  {toSEq := Q, PredSubst := Ps, Refl := R}

namespace LEq

instance [K : LEq L T] 
  : Logos.PredSubst L K.toFun := K.PredSubst

-- PredSubst
abbrev predSubst (K : LEq L T) 
  {F a b} := K.PredSubst.toFun F a b

-- FunSubst
abbrev FunSubst (K : LEq L T) 
  : FunSubst L K.toFun := iFunSubstByReflPredSubst
abbrev funSubst (K : LEq L T) 
  {f a b} := K.FunSubst.toFun f a b

end LEq
