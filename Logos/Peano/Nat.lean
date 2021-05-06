import Logos.Prelude.Newtype

universes u v
variable {P : Sort u} {T : Sort v} 

namespace Logos.Peano

class funtype SNat (P : Sort u) (T : Sort v) := 
  mem : T -> P

abbrev nat [N : SNat P T] := N.mem

namespace SNat

def «Prop» (N : SNat P T) := P
def Term (N : SNat P T) := T
def Pred (N : SNat P T) := T -> P
