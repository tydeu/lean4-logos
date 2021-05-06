import Logos.Math.Syntax

universes u v

namespace Logos.Peano

class IsNat (prop : Sort u) (form : Sort v) := 
  (isNat : form -> prop)

namespace IsNat

abbrev nat {P : Sort u} {T : Sort v} [C : IsNat P T] := C.isNat

def prop {P : Sort u} {T : Sort v} (N : IsNat P T) := P
def form {P : Sort u} {T : Sort v} (N : IsNat P T) := T
def pred {P : Sort u} {T : Sort v} (N : IsNat P T) := T -> P

end IsNat

export IsNat (nat)
