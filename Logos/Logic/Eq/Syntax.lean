import Logos.Prelude.Newtype
import Logos.Prelude.FunTypes

universes u v
variable {P : Sort u} {T : Sort v}

namespace Logos 

class funtype SEq (P : Sort u) (T : Sort v) : Rel P T
class funtype SNe (P : Sort u) (T : Sort v) : Rel P T

@[defaultInstance low] instance iPropEq : SEq Prop T := pack Eq
@[defaultInstance low] instance iPropNe : SNe Prop T := pack Ne

abbrev eq [K : SEq P T] := unpack K
abbrev ne [K : SNe P T] := unpack K

namespace Notation

scoped infix:50 (name := syntaxEq)  (priority := default + default) " = "  => SEq.toFun
scoped infix:50 (name := syntaxNe)  (priority := default + default) " /= " => SNe.toFun
scoped infix:50 (name := syntaxNe') (priority := default + default) " ≠ "  => SNe.toFun

macro_rules (kind := syntaxEq)  | `($x = $y)  => `(binrel% SEq.toFun $x $y)
macro_rules (kind := syntaxNe)  | `($x /= $y) => `(binrel% SNe.toFun $x $y)
macro_rules (kind := syntaxNe') | `($x ≠ $y)  => `(binrel% SNe.toFun $x $y)
