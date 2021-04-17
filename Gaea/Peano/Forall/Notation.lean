import Gaea.Peano.Forall.Syntax

open Lean

macro "∀ℕ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `pForallNat xs b
macro "forallNat" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `pForallNat xs b

-- Required for the unexpanders work
export Gaea.Peano (pForallNat)

@[appUnexpander Gaea.Peano.pForallNat] 
def unexpandForallNat : Lean.PrettyPrinter.Unexpander
  | `(pForallNat fun $x:ident => ∀ℕ $xs:binderIdent* => $b)
    => `(∀ℕ $x:ident $xs:binderIdent* => $b)
  | `(pForallNat fun $x:ident => $b)
    => `(∀ℕ $x:ident => $b)
  | `(pForallNat fun ($x:ident : $t) => $b)              
    => `(∀ℕ ($x:ident : $t) => $b)
  | _  => throw ()
