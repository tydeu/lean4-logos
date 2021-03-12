namespace Gaea.Syntax

class Zero (N : Sort u) := 
  (zero : N)

export Zero (zero)

@[defaultInstance 1]
instance {N : Type u} [C : Zero N] : OfNat N (natLit! 0) := 
  {ofNat := C.zero}

class Succ (N : Sort u) :=
  (S : N -> N)

export Succ (S)

end Gaea.Syntax
