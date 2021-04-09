import Gaea.Logic.Quant.Syntax

open Lean
open Gaea.Logic

macro "∀ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `lForall xs b
macro "forall " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `lForall xs b

macro "∃ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `lExists xs b
macro "exists " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `lExists xs b

-- Required for the unexpanders to work
export Gaea.Logic.LForall (lForall)
export Gaea.Logic.LExists (lExists)

@[appUnexpander Gaea.Logic.LForall.lForall] 
def unexpandLForall : Lean.PrettyPrinter.Unexpander
  | `(lForall fun $x:ident => ∀ $xs:binderIdent* => $b)
    => `(∀ $x:ident $xs:binderIdent* => $b)
  | `(lForall fun $x:ident => $b)
    => `(∀ $x:ident => $b)
  | `(lForall fun ($x:ident : $t) => $b)              
    => `(∀ ($x:ident : $t) => $b)
  | _  => throw ()

@[appUnexpander Gaea.Logic.LExists.lExists] 
def unexpandLExists : Lean.PrettyPrinter.Unexpander
  | `(lExists fun $x:ident => ∃ $xs:binderIdent* => $b)
    => `(∃ $x:ident $xs:binderIdent* => $b)
  | `(lExists fun $x:ident => $b)          
    => `(∃ $x:ident => $b)
  | `(lExists fun ($x:ident : $t) => $b)
    => `(∃ ($x:ident : $t) => $b)
  | _ => throw ()
