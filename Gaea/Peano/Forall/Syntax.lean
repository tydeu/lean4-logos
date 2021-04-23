import Gaea.Peano.Nat
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Quant.Syntax

universes u v

open Gaea.Notation
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

namespace Notation

open Lean

scoped macro "∀ℕ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `pForallNat xs b
scoped macro "forallNat" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `pForallNat xs b

@[appUnexpander Gaea.Peano.pForallNat] 
def unexpandForallNat : Lean.PrettyPrinter.Unexpander
  | `(pForallNat fun $x:ident => ∀ℕ $xs:binderIdent* => $b)
    => `(∀ℕ $x:ident $xs:binderIdent* => $b)
  | `(pForallNat fun $x:ident => $b)
    => `(∀ℕ $x:ident => $b)
  | `(pForallNat fun ($x:ident : $t) => $b)              
    => `(∀ℕ ($x:ident : $t) => $b)
  | _  => throw ()
