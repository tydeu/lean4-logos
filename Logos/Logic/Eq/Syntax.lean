import Logos.Prelude.Newtype
import Logos.Prelude.FunTypes

universes u v
variable {P : Sort u} {T : Sort v}

namespace Logos 

class funtype SEq (P : Sort u) (T : Sort v) := export eq : Rel P T
class funtype SNe (P : Sort u) (T : Sort v) := export ne : Rel P T

@[defaultInstance low] instance iEqOfProp : SEq Prop T := pack Eq
@[defaultInstance low] instance iNeOfProp : SNe Prop T := pack Ne

namespace Notation

scoped infix:50 (priority := default + default) " = "  => eq
scoped infix:50 (priority := default + default) " /= " => ne
scoped infix:50 (priority := default + default) " ≠ "  => ne

macro_rules | `($x = $y)  => `(binrel% eq $x $y)
macro_rules | `($x /= $y) => `(binrel% ne $x $y)
macro_rules | `($x ≠ $y)  => `(binrel% ne $x $y)
