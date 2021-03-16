import Gaea.Syntax.Math

universes u v

open Gaea.Syntax

namespace Gaea.Peano

class IsNat (prop : Sort u) (form : Sort v) := 
  (isNat : form -> prop)

namespace IsNat

abbrev nat {P : Sort u} {T : Sort v} [C : IsNat P T] := C.isNat

def prop {P : Sort u} {T : Sort v} (N : IsNat P T) := P
def form {P : Sort u} {T : Sort v} (N : IsNat P T) := T
def pred {P : Sort u} {T : Sort v} (N : IsNat P T) := T -> P

end IsNat

export IsNat (nat)

class Nat (P : Sort u) (T : Sort v) extends IsNat P T, Zero T, Succ T

namespace Nat

def prop {P : Sort u} {T : Sort v} (N : Nat P T) := P
def form {P : Sort u} {T : Sort v} (N : Nat P T) := T
def pred {P : Sort u} {T : Sort v} (N : Nat P T) := T -> P

def nat {P : Sort u} {T : Sort v} (N : Nat P T) := N.toIsNat.isNat
def isNat {P : Sort u} {T : Sort v} (N : Nat P T) := N.toIsNat.isNat
def zero {P : Sort u} {T : Sort v} (N : Nat P T) := N.toZero.zero
def succ {P : Sort u} {T : Sort v} (N : Nat P T) := N.toSucc.succ

end Nat

end Gaea.Peano
