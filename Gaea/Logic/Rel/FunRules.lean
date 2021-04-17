import Gaea.Logic.Judgment
import Gaea.Logic.Fun.Types
import Gaea.Logic.Rel.Type

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Commutativity
-- R (f a b) (f b a)
--------------------------------------------------------------------------------

-- Unconstrained

class CommOver (L : Logic P) (R : Rel P T) (f : Binar T) :=
  commOver : (a b : T) -> (L |- R (f a b) (f b a))

def commOver {L : Logic P} {R : Rel P T} {f} 
  [K : CommOver L R f] {a b} := K.commOver a b

-- Constrained

class CommOverT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  commOverT : (a b : T) -> (L |- C a) -> (L |- C b) -> (L |- R (f a b) (f b a))

def commOverT {L : Logic P} {R : Rel P T} {C f}
  [K : CommOverT L R C f] {a b} := K.commOverT a b

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- Left-to-Right
-- R (f (f a b) c) (f a (f b c))

-- Unconstrained
class LtrAssocOver (L : Logic P) (R : Rel P T) (f : Binar T) :=
  ltrAssocOver :  (a b c : T) ->  (L |- R (f (f a b) c) (f a (f b c)))

def ltrAssocOver {L : Logic P} {R : Rel P T} {f}
  [K : LtrAssocOver L R f] {a b c} := K.ltrAssocOver a b c

-- Constrained
class LtrAssocOverT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  ltrAssocOverT :  (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R (f (f a b) c) (f a (f b c)))

def ltrAssocOverT {L : Logic P} [R : Rel P T] {C f}
  [K : LtrAssocOverT L R C f] {a b c} := K.ltrAssocOverT a b c

-- Right-to-Left
-- R (f a (f b c)) (f (f a b) c)

-- Unconstrained
class RtlAssocOver (L : Logic P) (R : Rel P T) (f : Binar T) :=
  rtlAssocOver :  (a b c : T) ->  (L |- R (f a (f b c)) (f (f a b) c))

def rtlAssocOver {L : Logic P} {R : Rel P T} {f}
  [K : RtlAssocOver L R f] {a b c} := K.rtlAssocOver a b c

-- Constrained
class RtlAssocOverT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  rtlAssocOverT :  (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R (f a (f b c)) (f (f a b) c))

def rtlAssocOverT {L : Logic P} [R : Rel P T] {C f}
  [K : RtlAssocOverT L R C f] {a b c} := K.rtlAssocOverT a b c


end Gaea.Logic
