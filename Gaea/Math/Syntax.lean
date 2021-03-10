namespace Gaea.Math

class Zero (N : Sort u) := 
  (zero : N)

export Zero (zero)

instance {N : Type u} [C : Zero N] : OfNat N (natLit! 0) := 
  {ofNat := C.zero}

class Succ (N : Sort u) :=
  (succ : N -> N)

export Succ (succ)

@[reducible] def Shorthand.S {N : Type u} [Succ N] (n : N) := succ n

end Gaea.Math
