import Gaea.Logic.Logic
import Gaea.Logic.Dual.Rules
import Gaea.Logic.Dual.Theorems
import Gaea.Logic.Unit.Modules

universe u
variable {P : Sort u}

namespace Gaea.Logic

variable {L : Logic P}

--------------------------------------------------------------------------------
-- Implication 
--------------------------------------------------------------------------------

class LImp (L : Logic P) (lneg : Unar P) extends LEnt L :=
  ByContraposition : ByContraposition L toFun lneg
  ModusTollens : ModusTollens L toFun lneg

instance iLImp {L : Logic P} [larr : LArr P] {lneg : Unar P} 
  [C : Condition L larr.toFun] [Mp : ModusPonens L larr.toFun] 
  [ByC : ByContraposition L larr.toFun lneg] [Mt : ModusTollens L larr.toFun lneg] 
  : LImp L lneg := 
  {toLArr := larr, Condition := C, ModusPonens := Mp, 
    ByContraposition := ByC, ModusTollens := Mt}

namespace LImp

variable {lneg : Unar P}
abbrev funType (K : LImp L lneg) := Binar P
instance : CoeFun (LImp L lneg) funType := {coe := fun K => K.toFun}

instance [K : LImp L lneg] : 
  Logic.ByContraposition L K.toFun lneg := K.ByContraposition
instance [K : LImp L lneg] : 
  Logic.ModusTollens L K.toFun lneg := K.ModusTollens

-- Basic
abbrev byContraposition (K : LImp L lneg) 
  {p q} := K.ByContraposition.toFun p q
abbrev mt (K : LImp L lneg) 
  {p q} := K.ModusTollens.toFun p q

end LImp

--------------------------------------------------------------------------------
-- Material Biconditional (Iff)
--------------------------------------------------------------------------------

class MIff (L : Logic P) (lneg : Unar P) extends LIff L :=
  LeftMt : LeftMt L toFun lneg
  RightMt : RightMt L toFun lneg

instance iMIff {L : Logic P} {lneg : Unar P}
  [iff : SIff P] [B : Bicondition L iff.toFun] 
  [Mpl : LeftMp L iff.toFun] [Mpr : RightMp L iff.toFun]
  [Mtl : LeftMt L iff.toFun lneg] [Mtr : RightMt L iff.toFun lneg] 
  : MIff L lneg := 
  {toSIff := iff, Bicondition := B, LeftMp := Mpl, RightMp := Mpr, 
    LeftMt := Mtl, RightMt := Mtr}

namespace MIff

variable {lneg : Unar P}
abbrev funType (K : MIff L lneg) := Binar P
instance : CoeFun (MIff L lneg) funType := {coe := fun K => K.toFun}

instance [K : MIff L lneg] :
  Logic.LeftMt L K.toFun lneg := K.LeftMt
instance [K : MIff L lneg] :
  Logic.RightMt L K.toFun lneg := K.RightMt

-- Basic
abbrev leftMt (K : MIff L lneg) 
  {p q} := K.LeftMt.toFun p q
abbrev mt (K : MIff L lneg) 
  {p q} := K.LeftMt.toFun p q
abbrev rightMt (K : MIff L lneg) 
  {p q} := K.RightMt.toFun p q
abbrev mtr (K : MIff L lneg) 
  {p q} := K.RightMt.toFun p q

end MIff

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

class LDisj (L : Logic P) (lneg : Unar P) extends LAlt L :=
  LeftMtp : LeftMtp L toFun lneg
  RightMtp : RightMtp L toFun lneg

instance iLDisj {L : Logic P} [Dj: Disj P] {lneg}
  [ByE : ByEither L Dj.toFun]  [SLess : LeftTaut L Dj.toFun] [RT : RightTaut L Dj.toFun] 
  [LMtp : LeftMtp L Dj.toFun lneg] [RMtp : RightMtp L Dj.toFun lneg] 
  : LDisj L lneg := 
  {toDisj := Dj, ByEither := ByE, 
    LeftTaut := SLess, RightTaut := RT, LeftMtp := LMtp, RightMtp := RMtp}

namespace LDisj

variable {lneg : Unar P}
abbrev funType (K : LDisj L lneg) := Binar P
instance : CoeFun (LDisj L lneg) funType := {coe := fun K => K.toFun}

instance [K : LDisj L lneg] :
  Logic.LeftMtp L K.toFun lneg := K.LeftMtp
instance [K : LDisj L lneg] :
  Logic.RightMtp L K.toFun lneg := K.RightMtp

-- Basic
abbrev leftMtp (K : LDisj L lneg)
  {p q} := K.LeftMtp.toFun p q
abbrev mtp (K : LDisj L lneg)
  {p q} := K.LeftMtp.toFun p q
abbrev rightMtp (K : LDisj L lneg)
  {p q} := K.RightMtp.toFun p q
abbrev mtpr (K : LDisj L lneg)
  {p q} := K.RightMtp.toFun p q

end LDisj

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

class LNot (L : Logic P) extends LNeg P :=
  AdFalso : AdFalso L toFun
  Noncontradiction : Noncontradiction L toFun

instance iLNot {L : Logic P} [Nt : LNeg P] 
  [Af : AdFalso L Nt.toFun] [Nc : Noncontradiction L Nt.toFun] : LNot L := 
  {toLNeg := Nt, AdFalso := Af, Noncontradiction := Nc}

namespace LNot

abbrev funType (K : LNot L) := Unar P
instance : CoeFun (LNot L) funType := {coe := fun K => K.toFun}

instance [K : LNot L] : 
  Logic.AdFalso L K.toFun := K.AdFalso
instance [K : LNot L] : 
  Logic.Noncontradiction L K.toFun := K.Noncontradiction

-- Basic
abbrev adFalso (K : LNot L) 
  {p} := K.AdFalso.toFun p
abbrev intro (K : LNot L) 
  {p} := K.AdFalso.toFun p
abbrev noncontradiction (K : LNot L) 
  {p} := K.Noncontradiction.toFun p
abbrev elim (K : LNot L) 
  {p} := K.Noncontradiction.toFun p

end LNot
