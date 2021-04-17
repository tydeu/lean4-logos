import Gaea.Logic.Quant.Type

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

-- Forall

class SForall (P : Sort u) (T : Sort v) :=
  toFun : Quant P T

namespace SForall
abbrev funType (K : SForall P T) := Quant P T
instance : CoeFun (SForall P T) funType := {coe := fun K => K.toFun}
end SForall

abbrev lForall [K : SForall P T] := K.toFun

-- Exists

class SExists (P : Sort u) (T : Sort v) :=
  toFun : Quant P T

namespace SExists
abbrev funType (K : SExists P T) := Quant P T
instance : CoeFun (SExists P T) funType := {coe := fun K => K.toFun}
end SExists

abbrev lExists [K : SExists P T] := K.toFun

end Gaea.Logic
