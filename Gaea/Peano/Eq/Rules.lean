import Gaea.Logic
import Gaea.Syntax
import Gaea.Peano.Nat

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano

-- (b = a) /\ (c = a) -> (b = c)

class EqNatLeftEuc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatLeftEuc : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c))

def eqNatLeftEuc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [C : EqNatLeftEuc L N Q] {a b c : T} := C.eqNatLeftEuc a b c 

-- (a = b) /\ (a = c) -> (b = c)

class EqNatRightEuc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatRightEuc : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- a = b) -> (L |- a = c) -> (L |- b = c))

def eqNatRightEuc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [C : EqNatLeftEuc L N Q] {a b c : T} := C.eqNatLeftEuc a b c 
  
end Gaea.Peano
