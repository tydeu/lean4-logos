import Gaea.Logic.Basic
import Gaea.Logic.Syntax

-- Judgements

infix:10 " |- " => Gaea.Logic.proof
infix:10 " ⊢ " => Gaea.Logic.proof

-- Connectives

infixr:25 " -> " => Gaea.Logic.If.if'
infixr:25 " ⇒ " => Gaea.Logic.If.if'

infix:20 " <-> " => Gaea.Logic.Iff.iff
infix:20 " ⇔ "  => Gaea.Logic.Iff.iff

infixr:35 " /\\ " => Gaea.Logic.And.and
infixr:35 " ∧ "   => Gaea.Logic.And.or
infixr:30 " \\/ " => Gaea.Logic.Or.or
infixr:30 " ∨ "   => Gaea.Logic.Or.or

-- Equality

infix:50 " = "  => Gaea.Logic.Eq.eq

-- Quantifiers

open Lean

macro "∀" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `Gaea.Logic.Forall.forall' xs b
macro "forall" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `Gaea.Logic.Forall.forall' xs b

macro "∃" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `Gaea.Logic.Exists.exists' xs b
macro "exists" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `Gaea.Logic.Exists.exists' xs b
