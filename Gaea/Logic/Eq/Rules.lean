import Gaea.Logic.Judgment
import Gaea.Logic.Rel.Rules
import Gaea.Logic.Eq.Syntax
import Gaea.Logic.Eq.Notation

universes u v

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

-- (x = a) /\ (y = b) /\ (a = b) -> (x = y)

class EqJoinT {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P) :=
  (eqJoinT : (x y a b : T) -> 
    (L |- C x) -> (L |- C y) -> (L |- C a) -> (L |- C b) ->
    (L |- x = a) -> (L |- y = b) -> (L |- a = b) -> (L |- x = y))

instance iRelJoinTOfEqJoinT 
{P : Sort u} {T : Sort v}  {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqJoinT L Q C] : RelJoinT L Q.eq C := {relJoinT := K.eqJoinT}

instance iEqJoinTOfRelJoinT 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : RelJoinT L Q.eq C] : EqJoinT L Q C := {eqJoinT := K.relJoinT}

def eqJoinT 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqJoinT L Q C] {x y a b : T} := K.eqJoinT x y a b 

-- (a = b) /\ (x = a) /\ (y = b) -> (x = y)

def eqJoinT' 
{P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqJoinT L Q C] {a b x y : T}
:= fun Ca Cb Cx Cy Qab Qxa Qyb => K.eqJoinT x y a b Cx Cy Ca Cb Qxa Qyb Qab

--------------------------------------------------------------------------------
-- Function Substitution
-- (a = b) -> (f a = f b)
--------------------------------------------------------------------------------

-- Constrained for a given function
class EqToEqFunT {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T) :=
  (eqToEqFunT : (a b : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- a = b) -> (L |- f a = f b))

instance iEqToEqFunTOfFSubst {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T} [K : FSubst L Q.eq f] 
: EqToEqFunT L Q C f := {eqToEqFunT := fun a b _ _  => K.fSubst a b}

def eqToEqFunT {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T}
[K : EqToEqFunT L Q C f] {a b : T} := K.eqToEqFunT a b

--------------------------------------------------------------------------------
-- Magma Addition / Substitution
--------------------------------------------------------------------------------

-- Left Addition / Right Substitution
-- (a = b) -> (f c a = f c b)

class EqMagLeftT {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T -> T)  :=
  (eqMagLeftT : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- a = b) -> (L |- f c a = f c b))

def eqMagLeftT {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T}
[K : EqMagLeftT L Q C f] {a b c : T} := K.eqMagLeftT a b c

def eqMagLeftT' {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T} 
[K : EqMagLeftT L Q C f] {c a b : T} 
(Nc : L |- C c) (Na : L |- C a) (Nb : L|- C b) 
:= K.eqMagLeftT a b c Na Nb Nc

-- Right Addition / Left Substitution
-- (a = b) -> (f a c = f b c)

class EqMagRightT {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T -> T)  :=
  (eqMagRightT : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- a = b) -> (L |- f a c = f b c))

def eqMagRightT {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T}
[K : EqMagRightT L Q C f] {a b c : T} := K.eqMagRightT a b c

def eqMagRightT' {P : Sort u} {T : Sort v} 
{L : Logic P}  [Q : LEq P T] {C : T -> P} {f : T -> T -> T} 
[K : EqMagRightT L Q C f] {c a b : T} 
(Nc : L |- C c) (Na : L |- C a) (Nb : L|- C b) 
:= K.eqMagRightT a b c Na Nb Nc
  
end Gaea.Logic
