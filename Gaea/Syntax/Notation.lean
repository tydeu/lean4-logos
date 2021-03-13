import Gaea.Syntax.Math
import Gaea.Syntax.Logic

open Gaea.Syntax

-- Functions

export Gaea.Syntax.Succ (S)

-- Connectives

infixr:25 " -> "  => LIf.lif
infixr:25 " ⇒ "   => LIf.lif

infix:20 " <-> "  => LIff.liff
infix:20 " ⇔ "   => LIff.liff

infixr:35 " /\\ " => LAnd.land
infixr:35 " ∧ "   => LAnd.land
infixr:30 " \\/ " => LOr.lor
infixr:30 " ∨ "   => LOr.lor

-- Equality

infix:50 " = "  => LEq.leq

-- Quantifiers

open Lean

macro "∀ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `LForall.lForall xs b
macro "forall" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `LForall.lForall xs b

macro "∃ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `lExists xs b
macro "exists" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `lExists xs b

-- Required for the unexpanders work
export Gaea.Syntax.LForall (lForall)
export Gaea.Syntax.LExists (lExists)

@[appUnexpander Gaea.Syntax.LForall.lForall] 
def unexpandLForall : Lean.PrettyPrinter.Unexpander
  | `(lForall fun $x:ident => ∀ $xs:binderIdent* => $b)
    => `(∀ $x:ident $xs:binderIdent* => $b)
  | `(lForall fun $x:ident => $b)
    => `(∀ $x:ident => $b)
  | `(lForall fun ($x:ident : $t) => $b)              
    => `(∀ ($x:ident : $t) => $b)
  | _  => throw ()

@[appUnexpander Gaea.Syntax.LExists.lExists] 
def unexpandLExists : Lean.PrettyPrinter.Unexpander
  | `(lExists fun $x:ident => ∃ $xs:binderIdent* => $b)
    => `(∃ $x:ident $xs:binderIdent* => $b)
  | `(lExists fun $x:ident => $b)          
    => `(∃ $x:ident => $b)
  | `(lExists fun ($x:ident : $t) => $b)
    => `(∃ ($x:ident : $t) => $b)
  | _ => throw ()
