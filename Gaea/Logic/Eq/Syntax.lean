import Gaea.Logic.Rel.Type

universes u v

namespace Gaea.Logic 

class SEq (P : Sort u) (T : Sort v) :=
  toFun : Rel P T

abbrev eq {P : Sort u} {T : Sort v} 
  [K : SEq P T] := K.toFun

namespace SEq
variable {P : Sort u} {T : Sort v}
abbrev funType (K : SEq P T) := Rel P T
instance : CoeFun (SEq P T) funType := {coe := fun K => K.toFun}
end SEq

namespace Notation
scoped infix:50 " = " => Gaea.Logic.SEq.toFun
