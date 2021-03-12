import Gaea.Syntax.Logic

-- Connectives

infixr:25 " -> " => Gaea.Syntax.LIf.lif
infixr:25 " ⇒ " => Gaea.Syntax.LIf.lif

infix:20 " <-> " => Gaea.Syntax.LIff.liff
infix:20 " ⇔ "  => Gaea.Syntax.LIff.liff

infixr:35 " /\\ " => Gaea.Syntax.LAnd.land
infixr:35 " ∧ "   => Gaea.Syntax.LAnd.lor
infixr:30 " \\/ " => Gaea.Syntax.LOr.lor
infixr:30 " ∨ "   => Gaea.Syntax.LOr.lor

-- Equality

infix:50 " = "  => Gaea.Syntax.LEq.leq

-- Quantifiers

open Lean

macro "∀" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `Gaea.Syntax.LForall.lForall xs b
macro "forall" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `Gaea.Syntax.LForall.lForall xs b

macro "∃" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `Gaea.Syntax.LExists.lExists xs b
macro "exists" xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders `Gaea.Syntax.LExists.lExists xs b
