import Gaea.Logic.Rel.Type

universes u v

namespace Gaea.Logic 

class SEq (P : Sort u) (T : Sort v) :=
  toFun : Rel P T

namespace SEq
variable {P : Sort u} {T : Sort v}
abbrev funType (K : SEq P T) := Rel P T
instance : CoeFun (SEq P T) funType := {coe := fun K => K.toFun}
end SEq

abbrev eq {P : Sort u} {T : Sort v} [K : SEq P T] := K.toFun

end Gaea.Logic
