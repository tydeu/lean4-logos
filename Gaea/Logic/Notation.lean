import Gaea.Logic.Logic
import Gaea.Logic.Eq.Syntax
import Gaea.Logic.Basic.Syntax

open Gaea.Logic

-- Judgements

infix:10 " |- " => Judgment
infix:10 " ⊢ " => Judgment

-- Boolean Constants

def true {P : Sort u} [K : LTrue P] := K.lTrue
def false {P : Sort u} [K : LFalse P] := K.lFalse

-- Connectives

infixr:25 " -> "  => LIf.lIf
infixr:25 " ⇒ "   => LIf.lIf

infix:20 " <-> "  => LIff.lIff
infix:20 " ⇔ "   => LIff.lIff

infixr:35 " /\\ " => LAnd.lAnd
infixr:35 " ∧ "   => LAnd.lAnd
infixr:30 " \\/ " => LOr.lOr
infixr:30 " ∨ "   => LOr.lOr

prefix "~" => LNot.lNot
prefix "¬" => LNot.lNot

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
