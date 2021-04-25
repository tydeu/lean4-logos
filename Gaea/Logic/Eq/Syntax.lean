import Gaea.FunTypes

universes u v

namespace Gaea 

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
scoped infix:50 (name := syntaxEq) " = " => SEq.toFun
macro_rules (kind := syntaxEq)  | `($x = $y)  => `(binrel% eq $x $y)
