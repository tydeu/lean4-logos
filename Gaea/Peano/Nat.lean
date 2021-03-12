universes u v

namespace Gaea.Peano

class Nat (prop : Sort u) (form : Sort v) := 
  (nat : form -> prop)

export Nat (nat)

namespace Nat

def prop {P : Sort u} {T : Sort v} (N : Nat P T) := P
def form {P : Sort u} {T : Sort v} (N : Nat P T) := T
def pred {P : Sort u} {T : Sort v} (N : Nat P T) := T -> P

end Nat

end Gaea.Peano
