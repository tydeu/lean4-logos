import Gaea.Logic.Notation
import Gaea.Logic.Rel.Rules

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
[K : EqJoinT L Q C] : RelJoinT L Q.lEq C := {relJoinT := K.eqJoinT}

instance iEqJoinTOfRelJoinT 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : RelJoinT L Q.lEq C] : EqJoinT L Q C := {eqJoinT := K.relJoinT}

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
-- Commutativity
--------------------------------------------------------------------------------

-- f a b = f b a

-- Unconstrained for a given function
class Comm {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (f : T -> T -> T) :=
  (comm : (a b : T) -> (L |- f a b = f b a))

def comm {P : Sort u} {T : Sort v} 
{L : Logic P} (Q : LEq P T) {f : T -> T -> T}
[K : Comm L Q f] {a b : T} := K.comm a b

-- Constrained for a given function
class CommT {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T -> T) :=
  (commT : (a b : T) -> (L |- C a) -> (L |- C b) -> (L |- f a b = f b a))

def commT {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T}
[K : CommT L Q C f] {a b : T} := K.commT a b

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- f (f a b) c = f a (f b c)

-- Unconstrained for a given function
class Assoc {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (f : T -> T -> T) :=
  (assoc :  (a b c : T) ->  (L |- (f (f a b) c) = (f a (f b c))))

def assoc {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {f : T -> T -> T}
[K : Assoc L Q f] {a b c : T} := K.assoc a b c

-- Constrained for a given function
class AssocT {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T -> T) :=
  (assocT :  (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- (f (f a b) c) = (f a (f b c))))

def assocT {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T}
[K : AssocT L Q C f] {a b c : T} := K.assocT a b c

--------------------------------------------------------------------------------
-- Function Substitution
-- (a = b) -> (f a = f b)
--------------------------------------------------------------------------------

-- Unconstrained
class EqFunSubst {P : Sort u} {T : Sort v} (L : Logic P) (Q : LEq P T) :=
  (eqFunSubst : (a b : T) -> (f : T -> T) ->
    (L |- a = b) -> (L |- f a = f b))

instance iFunSubstOfEqFunSubst 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqFunSubst L Q] : FunSubst L Q.lEq
:= {funSubst := K.eqFunSubst}

instance iEqFunSubstOfFunSubst 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : FunSubst L Q.lEq] : EqFunSubst L Q
:= {eqFunSubst := K.funSubst}

def eqFunSubst 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqFunSubst L Q] {a b : T} {f : T -> T} := K.eqFunSubst a b f

def eqFunSubst' 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqFunSubst L Q] {a b : T} := K.eqFunSubst a b

-- Constrained for a given function
class EqToEqFunT {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T) :=
  (eqToEqFunT : (a b : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- a = b) -> (L |- f a = f b))

instance iEqToEqFunTOfEqFunSubst {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T}
[K : EqFunSubst L Q] : EqToEqFunT L Q C f
:= {eqToEqFunT := fun a b _ _  => K.eqFunSubst a b f}

def eqToEqFunT {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T}
[K : EqToEqFunT L Q C f] {a b : T} := K.eqToEqFunT a b

--------------------------------------------------------------------------------
-- Predicate Substitution
-- (a = b) -> (P a -> P b)
--------------------------------------------------------------------------------

class EqPredSubst {P : Sort u} {T : Sort v} (L : Logic P) (Q : LEq P T) :=
  (eqPredSubst : (a b : T) -> (f : T -> P) -> 
    (L |- a = b) -> (L |- f a) -> (L |- f b))

instance iPredSubstOfEqPredSubst 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqPredSubst L Q] : PredSubst L Q.lEq
:= {predSubst := K.eqPredSubst}

instance iEqPredSubstOfPredSubst
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : PredSubst L Q.lEq] : EqPredSubst L Q
:= {eqPredSubst := K.predSubst}

def eqPredSubst 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqPredSubst L Q] {a b : T} {f : T -> P} := K.eqPredSubst a b f

def eqPredSubst' 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqPredSubst L Q] {a b : T} := K.eqPredSubst a b

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
