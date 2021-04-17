import Gaea.Peano.Nat
import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Prop.Notation
import Gaea.Logic.Quant.Syntax
import Gaea.Logic.Quant.Notation

universes u v

open Gaea.Logic

namespace Gaea.Peano

class SForallNat (P : Sort u) (T : Sort v) :=
  toFun : Quant P T

namespace SForallNat
variable {P : Sort u} {T : Sort v}
abbrev funType (K : SForallNat P T) := Quant P T
instance : CoeFun (SForallNat P T) funType := {coe := fun K => K.toFun}
end SForallNat

abbrev pForallNat {P : Sort u} {T : Sort v} [K : SForallNat P T] := K.toFun

def LForallIfNat {P : Sort u} {T : Sort v} 
  (N : IsNat P T) (Fa : SForall P T) (larr : LArr P) : 
  SForallNat P T := {toFun := fun f => forall a => nat a -> f a}

end Gaea.Peano