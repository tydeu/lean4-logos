import Gaea.Logic

namespace Gaea.Peano

class Nat (L : Logic) :=
  (form : Sort u)
  (is_nat : form -> L.prop)

class IsNat (prop : Sort u) (form : Sort v) := 
  (is_nat : form -> prop)

instance (L : Logic) (N : Nat L) : IsNat L.prop N.form :=
  {is_nat := N.is_nat}

export IsNat (is_nat)

def Shorthand.nat {L : Logic} {N : Nat L} := N.is_nat
open Shorthand (nat)

namespace Nat

def pred {L : Logic} (N : Nat L) :=
  N.form -> L.prop

def Sigma {L : Logic} (N : Nat L) := 
  _root_.Sigma (fun n : N.form => L.proof (nat n)) 

def sigma {L : Logic} (N : Nat L) : 
  (n : N.form) -> L.proof (nat n) -> N.Sigma := Sigma.mk

end Nat

end Gaea.Peano
