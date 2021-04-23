/-
  This module defines scoped locally-bound notation.
  If you `open Gaea.LocalNotation` and write `a = b`,
  it will translate to `eq a b` were `eq` will bind locally.
-/
namespace Gaea.LocalNotation

set_option hygiene false

-- Arrows

scoped infixr:25 " -> " => arr
scoped infixr:25 " → "  => arr
scoped infixr:25 " -> " => larr
scoped infixr:25 " ⇒ "  => larr

scoped infix:20 " <-> " => darr
scoped infix:20 " ↔ "   => darr
scoped infix:20 " <-> " => iff
scoped infix:20 " ⇔ "  => iff

-- Logical Connectives

scoped infixr:35 " /\\ " => conj
scoped infixr:35 " ∧ "   => conj
scoped infixr:30 " \\/ " => disj
scoped infixr:30 " ∨ "   => disj

scoped prefix:max "~"  => lneg
scoped prefix:max "¬"  => lneg

-- Binary Relations

scoped infix:50 (name := localEq)  " = "  => eq
scoped infix:50 (name := localLt)  " < "  => lt
scoped infix:50 (name := localLe)  " <= " => le
scoped infix:50 (name := localLe') " ≤ "  => le
scoped infix:50 (name := localGt)  " > "  => gt
scoped infix:50 (name := localGe)  " >= " => ge
scoped infix:50 (name := localGe') " ≥ "  => ge

macro_rules (kind := localEq)  | `($x = $y)  => `(binrel% eq $x $y)
macro_rules (kind := localLt)  | `($x < $y)  => `(binrel% lt $x $y)
macro_rules (kind := localLe)  | `($x <= $y) => `(binrel% le $x $y)
macro_rules (kind := localLe') | `($x ≤ $y)  => `(binrel% le $x $y)
macro_rules (kind := localGt)  | `($x > $y)  => `(binrel% gt $x $y)
macro_rules (kind := localGe)  | `($x >= $y) => `(binrel% ge $x $y)
macro_rules (kind := localGe') | `($x ≥ $y)  => `(binrel% ge $x $y)

-- Math Operators

scoped infixl:65 " + "  => add
scoped infixl:65 " - "  => sub
scoped infixl:70 " * "  => mul
scoped infixl:70 " / "  => div
scoped infixl:70 " % "  => mod
scoped infixr:80 " ^ "  => pow
scoped prefix:100 "-"   => neg

set_option hygiene true
