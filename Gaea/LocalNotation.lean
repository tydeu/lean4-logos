/-
  This module defines scoped locally-bound notation.
  If you `open Gaea.LocalNotation` and write `a = b`,
  it will translate to `eq a b` were `eq` will bind locally.
-/
namespace Gaea.LocalNotation

set_option hygiene false

-- Arrows

scoped infixr:25 (name := localArr)   (priority := default + default) " -> "  => arr
scoped infixr:25 (name := localArr')  (priority := default + default) " → "   => arr
scoped infixr:25 (name := localLArr)  (priority := default + default) " -> "  => larr
scoped infixr:25 (name := localLArr') (priority := default + default) " ⇒ "   => larr

scoped infix:20 (name := localDArr)   (priority := default + default) " <-> " => darr
scoped infix:20 (name := localDArr')  (priority := default + default) " ↔ "   => darr
scoped infix:20 (name := localIff)    (priority := default + default) " <-> " => iff
scoped infix:20 (name := localIff')   (priority := default + default) " ⇔ "  => iff

-- Logical Connectives

scoped infixr:35 (name := localConj)  (priority := default + default) " /\\ " => conj
scoped infixr:35 (name := localConj') (priority := default + default) " ∧ "   => conj
scoped infixr:30 (name := localDisj)  (priority := default + default) " \\/ " => disj
scoped infixr:30 (name := localDisj') (priority := default + default) " ∨ "   => disj

scoped prefix:max (name := localLNeg)  (priority := default + default) "~"  => lneg
scoped prefix:max (name := localLNeg') (priority := default + default) "¬"  => lneg

-- Binary Relations

scoped infix:50 (name := localEq)  (priority := default + default) " = "  => eq
scoped infix:50 (name := localLt)  (priority := default + default) " < "  => lt
scoped infix:50 (name := localLe)  (priority := default + default) " <= " => le
scoped infix:50 (name := localLe') (priority := default + default) " ≤ "  => le
scoped infix:50 (name := localGt)  (priority := default + default) " > "  => gt
scoped infix:50 (name := localGe)  (priority := default + default) " >= " => ge
scoped infix:50 (name := localGe') (priority := default + default) " ≥ "  => ge

macro_rules (kind := localEq)  | `($x = $y)  => `(binrel% eq $x $y)
macro_rules (kind := localLt)  | `($x < $y)  => `(binrel% lt $x $y)
macro_rules (kind := localLe)  | `($x <= $y) => `(binrel% le $x $y)
macro_rules (kind := localLe') | `($x ≤ $y)  => `(binrel% le $x $y)
macro_rules (kind := localGt)  | `($x > $y)  => `(binrel% gt $x $y)
macro_rules (kind := localGe)  | `($x >= $y) => `(binrel% ge $x $y)
macro_rules (kind := localGe') | `($x ≥ $y)  => `(binrel% ge $x $y)

-- Math Operators

scoped infixl:65  (name := localAdd) (priority := default + default) " + "  => add
scoped infixl:65  (name := localSub) (priority := default + default) " - "  => sub
scoped infixl:70  (name := localMul) (priority := default + default) " * "  => mul
scoped infixl:70  (name := localDiv) (priority := default + default) " / "  => div
scoped infixl:70  (name := localMod) (priority := default + default) " % "  => mod
scoped infixr:80  (name := localPow) (priority := default + default) " ^ "  => pow
scoped prefix:100 (name := localNeg) (priority := default + default) "-"    => neg

set_option hygiene true
