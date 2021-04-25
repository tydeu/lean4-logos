import Gaea.Logic.Logic
import Gaea.Logic.Quant.Rules
import Gaea.Logic.Quant.Syntax

namespace Gaea

universes u v
variable {P : Sort u} {T : Sort v}
variable {L : Logic P}

--------------------------------------------------------------------------------
-- Forall
--------------------------------------------------------------------------------

class LForall (L : Logic P) (T : Sort v) extends SForall P T :=
  UnivGen : UnivGen L toFun
  UnivInst : UnivInst L toFun

instance iLForall [Fa : SForall P T] 
  [G : UnivGen L Fa.toFun] [I : UnivInst L Fa.toFun] :
  LForall L T := {toSForall := Fa, UnivGen := G, UnivInst := I}

namespace LForall

abbrev funType (K : LForall L T) := Quant P T
instance : CoeFun (LForall L T) funType := {coe := fun K => K.toFun}

instance iUnivGenOfMForall [K : LForall L T] :
  Gaea.UnivGen L K.toFun := K.UnivGen
instance iUnivInstOfMForall [K : LForall L T] :
  Gaea.UnivInst L K.toFun := K.UnivInst

abbrev gen (K : LForall L T) 
  {f} := K.UnivGen.toFun f
abbrev intro (K : LForall L T) 
  {f} := K.UnivGen.toFun f
abbrev inst {L : Logic P} (K : LForall L T) 
  {f} := K.UnivInst.toFun f
abbrev elim {L : Logic P} (K : LForall L T) 
  {f} := K.UnivInst.toFun f

end LForall

--------------------------------------------------------------------------------
-- Exists
--------------------------------------------------------------------------------

class LExists (L : Logic P) (T : Sort v) extends SExists P T :=
  ExstGen : ExstGen L toFun
  ExstInst : ExstInst L toFun

instance iLExists [X : SExists P T] 
  [G : ExstGen L X.toFun] [I : ExstInst L X.toFun] :
  LExists L T := {toSExists := X, ExstGen := G, ExstInst := I}

namespace LExists

abbrev funType (K : LExists L T) := Quant P T
instance : CoeFun (LExists L T) funType := {coe := fun K => K.toFun}

instance [K : LExists L T] :
  Gaea.ExstGen L K.toFun := K.ExstGen
instance [K : LExists L T] :
  Gaea.ExstInst L K.toFun := K.ExstInst

abbrev gen {L : Logic P} (K : LExists L T) 
  {f} := K.ExstGen.toFun f
abbrev intro {L : Logic P} (K : LExists L T) 
  {f} := K.ExstGen.toFun f
abbrev inst {L : Logic P} (K : LExists L T) 
  {f} (Xf) {r} := K.ExstInst.toFun f Xf r
abbrev elim {L : Logic P} (K : LExists L T) 
  {f} (Xf) {r} := K.ExstInst.toFun f Xf r

end LExists
