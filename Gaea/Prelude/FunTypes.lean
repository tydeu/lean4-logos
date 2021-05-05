namespace Gaea

-- Endofunctions
abbrev Unar.{u} (A : Sort u) := A -> A
abbrev Binar.{u} (A : Sort u) := A -> A -> A
abbrev Ternar.{u} (A : Sort u) := A -> A -> A -> A

-- Logical functions
abbrev Pred.{u,v} (P : Sort u) (T : Sort v) := T -> P
abbrev Quant.{u,v} (P : Sort u) (T : Sort v) := (T -> P) -> P
abbrev HRel.{u,v,w} (P : Sort u) (X : Sort v) (Y : Sort w) := X -> Y -> P
abbrev Rel.{u,v} (P : Sort u) (T : Sort v) := T -> T -> P
