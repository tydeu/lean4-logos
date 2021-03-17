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

class PNat (P : Sort u) (T : Sort v) extends IsNat P T, Zero T, Succ T

namespace PNat

def prop {P : Sort u} {T : Sort v} (N : PNat P T) := P
def form {P : Sort u} {T : Sort v} (N : PNat P T) := T
def pred {P : Sort u} {T : Sort v} (N : PNat P T) := T -> P

abbrev nat {P : Sort u} {T : Sort v} (N : PNat P T) := N.toIsNat.isNat
abbrev isNat {P : Sort u} {T : Sort v} (N : PNat P T) := N.toIsNat.isNat
abbrev zero {P : Sort u} {T : Sort v} (N : PNat P T) := N.toZero.zero
abbrev succ {P : Sort u} {T : Sort v} (N : PNat P T) := N.toSucc.succ

end PNat

end Gaea.Peano
