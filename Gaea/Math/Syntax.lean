universes u v

namespace Gaea.Math

-- Numerics

class Zero (N : Sort u) :=
  (zero : N)

class One (N : Sort u) :=
  (one : N)

class Succ (N : Sort u) :=
  (succ : N -> N)

namespace Succ
abbrev S {N : Sort u} [K : Succ N] := K.succ
end Succ

-- Inequalities

class LT (P : Sort u) (N : Sort v) :=
  (lt : N -> N -> P)

class LE (P : Sort u) (N : Sort v)  :=
  (le : N -> N -> P)

end Gaea.Math
