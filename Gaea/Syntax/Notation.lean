import Gaea.Syntax.Math
import Gaea.Syntax.Logic

open Gaea.Syntax

-- Math

export Gaea.Syntax.Succ (S)

infix:50 " < "  => LT.lt

infix:50 " <= " => LE.le
infix:50 " ≤ "  => LE.le

-- Connectives

infixr:25 " -> "  => LIf.lIf
infixr:25 " ⇒ "   => LIf.lIf

infix:20 " <-> "  => LIff.lIff
infix:20 " ⇔ "   => LIff.lIff

infixr:35 " /\\ " => LAnd.lAnd
infixr:35 " ∧ "   => LAnd.lAnd
infixr:30 " \\/ " => LOr.lOr
infixr:30 " ∨ "   => LOr.lOr

-- Equality

infix:50 " = "  => LEq.lEq

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
