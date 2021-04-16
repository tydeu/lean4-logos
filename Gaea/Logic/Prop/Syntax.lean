import Gaea.Logic.Fun.Types

universe u
variable {P : Sort u}

namespace Gaea.Logic 

-- Constants

class LTrue (P : Sort u) :=
  toProp : P

abbrev true {P : Sort u} [K : LTrue P] := K.toProp

class LFalse (P : Sort u) :=
  toProp : P

abbrev false {P : Sort u} [K : LFalse P] := K.toProp

-- Connectives

class Imp (P : Sort u) :=
  toFun : Binar P

namespace Imp
abbrev funType (K : Imp P) := Binar P
instance : CoeFun (Imp P) funType := {coe := fun K => K.toFun}
end Imp

abbrev imp {P : Sort u} [K : Imp P] := K.toFun

class SIff (P : Sort u) :=
  toFun : Binar P

namespace SIff
abbrev funType (K : SIff P) := Binar P
instance : CoeFun (SIff P) funType := {coe := fun K => K.toFun}
end SIff

abbrev iff {P : Sort u} [K : SIff P] := K.toFun

class Conj (P : Sort u):=
  toFun : Binar P

namespace Conj
abbrev funType (K : Conj P) := Binar P
instance : CoeFun (Conj P) funType := {coe := fun K => K.toFun}
end Conj

abbrev conj {P : Sort u} [K : Conj P] := K.toFun

class Disj (P : Sort u) :=
  toFun : Binar P

namespace Disj
abbrev funType (K : Disj P) := Binar P
instance : CoeFun (Disj P) funType := {coe := fun K => K.toFun}
end Disj

abbrev disj {P : Sort u} [K : Disj P] := K.toFun

class LNeg (P : Sort u) :=
  toFun : Unar P

namespace LNeg
abbrev funType (K : LNeg P) := Unar P
instance : CoeFun (LNeg P) funType := {coe := fun K => K.toFun}
end LNeg

abbrev lneg {P : Sort u} [K : LNeg P] := K.toFun

end Gaea.Logic