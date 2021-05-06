import Logos.Prelude.Newtype

universes u v
variable {P : Sort u} {T : Sort v} 

namespace Logos.Peano

class funtype PNat (P : Sort u) (T : Sort v) := 
  mem : T -> P

abbrev nat [N : PNat P T] := N.mem

namespace PNat

def «Prop» (N : PNat P T) := P
def Term (N : PNat P T) := T
def Pred (N : PNat P T) := T -> P
