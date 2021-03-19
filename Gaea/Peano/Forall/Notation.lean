import Gaea.Peano.Forall.Syntax

open Lean
open Gaea.Peano

macro "∀ℕ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `ForallNat.xForallNat xs b
macro "forallNat" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `ForallNat.xForallNat xs b

-- Required for the unexpanders work
export Gaea.Peano.ForallNat (xForallNat)

@[appUnexpander Gaea.Peano.ForallNat.xForallNat] 
def unexpandForallNat : Lean.PrettyPrinter.Unexpander
  | `(xForallNat fun $x:ident => ∀ℕ $xs:binderIdent* => $b)
    => `(∀ℕ $x:ident $xs:binderIdent* => $b)
  | `(xForallNat fun $x:ident => $b)
    => `(∀ℕ $x:ident => $b)
  | `(xForallNat fun ($x:ident : $t) => $b)              
    => `(∀ℕ ($x:ident : $t) => $b)
  | _  => throw ()
