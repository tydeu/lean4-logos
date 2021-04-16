import Gaea.Peano.Nat
import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Prop.Notation
import Gaea.Logic.Quant.Syntax
import Gaea.Logic.Quant.Notation

universes u v

open Gaea.Logic

namespace Gaea.Peano

class ForallNat (P : Sort u) (T : Sort v) :=
  (xForallNat : (T -> P) -> P)

def LForallIfNat {P : Sort u} {T : Sort v}
  (N : IsNat P T) (Fa : LForall P T) (imp : Imp P) : ForallNat P T
  := {xForallNat := fun f => forall a => nat a -> f a}

end Gaea.Peano