namespace Gaea.Logic

universes u v

abbrev Unar (T : Sort u) := T -> T
abbrev Binar (T : Sort u) := T -> T -> T
abbrev Quant (P : Sort u) (T : Sort v) := (T -> P) -> P
abbrev Rel (P : Sort u) (T : Sort v) := T -> T -> P

end Gaea.Logic
