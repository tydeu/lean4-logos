import Gaea.Logic.Notation
import Gaea.Logic.Rel.Rules

universes u v

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Reflexivity
-- a -> (a = a)
--------------------------------------------------------------------------------

--  Unconstrained
class EqRefl {P : Sort u} {T : Sort v} (L : Logic P) (Q : LEq P T) :=
  (eqRefl : (a : T) -> (L |- a = a))

instance iEqReflToRefl 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqRefl L Q] : Refl L Q.lEq := {refl := K.eqRefl}

instance iReflToEqRefl 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : Refl L Q.lEq] : EqRefl L Q := {eqRefl := K.refl}

def eqRefl 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqRefl L Q] := K.eqRefl

def eqRefl' 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqRefl L Q] {a : T} := K.eqRefl a

-- Constrained
class EqMemRefl {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P) :=
  (eqMemRefl : (a : T) -> (L |- C a) -> (L |- a = a))

instance iEqMemReflToMemRefl 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemRefl L Q C] : MemRefl L Q.lEq C := {memRefl := K.eqMemRefl}

instance iMemReflToEqMemRefl 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : MemRefl L Q.lEq C] : EqMemRefl L Q C := {eqMemRefl := K.memRefl}

def eqMemRefl 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemRefl L Q C] {a : T} := K.eqMemRefl a

--------------------------------------------------------------------------------
-- Symmetry
-- (a = b) -> (b = a)
--------------------------------------------------------------------------------

-- Unconstrained
class EqSymm {P : Sort u} {T : Sort v} (L : Logic P) (Q : LEq P T) :=
  (eqSymm : (a b : T) -> (L |- a = b) -> (L |- b = a))

instance iEqSymmToSymm 
{P : Sort u} {T : Sort v}  {L : Logic P} [Q : LEq P T]
[K : EqSymm L Q] : Symm L Q.lEq := {symm := K.eqSymm}

instance iSymmToEqSymm 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : Symm L Q.lEq] : EqSymm L Q := {eqSymm := K.symm}

def eqSymm 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqSymm L Q] := K.eqSymm

-- Constrained
class EqMemSymm {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P) :=
  (eqMemSymm : (a b : T) -> 
    (L |- C a) -> (L |- C b) ->
    (L |- a = b) -> (L |- b = a))

instance iEqMemSymmToMemSymm 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemSymm L Q C] : MemSymm L Q.lEq C := {memSymm := K.eqMemSymm}

instance iMemSymmToEqMemSymm 
{P : Sort u} {T : Sort v}  {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : MemSymm L Q.lEq C] : EqMemSymm L Q C := {eqMemSymm := K.memSymm}

def eqMemSymm 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemSymm L Q C] {a b : T} := K.eqMemSymm a b 

--------------------------------------------------------------------------------
-- Transitivity
-- (a = b) /\ (b = c) -> (a = c)
--------------------------------------------------------------------------------

-- Unconstrained
class EqTrans {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) :=
  (eqTrans : (a b c : T) ->
    (L |- a = b) -> (L |- b = c) -> (L |- a = c))

instance iEqTransToTrans 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqTrans L Q] : Trans L Q.lEq := {trans := K.eqTrans}

instance iTransToEqTrans 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] 
[K : Trans L Q.lEq] : EqTrans L Q := {eqTrans := K.trans}

def eqTrans 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqTrans L Q] {a b c : T} := K.eqTrans a b c 

def eqTrans' 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqTrans L Q] {b a c : T} := K.eqTrans a b c

-- Constrained
class EqMemTrans {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P)  :=
  (eqMemTrans : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- a = b) -> (L |- b = c) -> (L |- a = c))

instance iEqMemTransToMemTrans 
{P : Sort u} {T : Sort v}  {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemTrans L Q C] : MemTrans L Q.lEq C := {memTrans := K.eqMemTrans}

instance iMemTransToEqMemTrans 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : MemTrans L Q.lEq C] : EqMemTrans L Q C := {eqMemTrans := K.memTrans}

def eqMemTrans 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemTrans L Q C] {a b c : T} := K.eqMemTrans a b c 

def eqMemTrans' 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P} 
[K : EqMemTrans L Q C] {b a c : T} (Cb : L |- C b) (Ca : L |- C a) (Cc : L |- C c)  
:= K.eqMemTrans a b c Ca Cb Cc

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

-- (b = a) /\ (c = a) -> (b = c)

class EqMemJoin {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P) :=
  (eqMemJoin : (x y a b : T) -> 
    (L |- C x) -> (L |- C y) -> (L |- C a) -> (L |- C b) ->
    (L |- x = a) -> (L |- y = b) -> (L |- a = b) -> (L |- x = y))

instance iEqMemJoinToRelMemJoin 
{P : Sort u} {T : Sort v}  {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemJoin L Q C] : RelMemJoin L Q.lEq C := {relMemJoin := K.eqMemJoin}

instance iRelMemJoinToEqMemJoin 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : RelMemJoin L Q.lEq C] : EqMemJoin L Q C := {eqMemJoin := K.relMemJoin}

def eqMemJoin 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemJoin L Q C] {x y a b : T} := K.eqMemJoin x y a b 

-- (a = b) /\ (x = a) /\ (y = b) -> (x = y)

def eqMemJoin' 
{P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemJoin L Q C] {a b x y : T}
:= fun Ca Cb Cx Cy Qab Qxa Qyb => K.eqMemJoin x y a b Cx Cy Ca Cb Qxa Qyb Qab

--------------------------------------------------------------------------------
-- Euclideaness
--------------------------------------------------------------------------------

-- Left Euclidean
-- (b = a) /\ (c = a) -> (b = c)

class EqMemLeftEuc {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P) :=
  (eqMemLeftEuc : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c))

instance iEqMemLeftEucToMemLeftEuc
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemLeftEuc L Q C] : MemLeftEuc L Q.lEq C 
:= {memLeftEuc := K.eqMemLeftEuc}

instance iMemLeftEucToEqMemLeftEuc 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : MemLeftEuc L Q.lEq C] : EqMemLeftEuc L Q C 
:= {eqMemLeftEuc := K.memLeftEuc}

def eqMemLeftEuc 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemLeftEuc L Q C] {a b c : T} := K.eqMemLeftEuc a b c 

-- Right Euclidean
-- (a = b) /\ (a = c) -> (b = c)

class EqMemRightEuc {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P) :=
  (eqMemRightEuc : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- a = b) -> (L |- a = c) -> (L |- b = c))

instance iEqMemRightEucToMemRightEuc
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemRightEuc L Q C] : MemRightEuc L Q.lEq C 
:= {memRightEuc := K.eqMemRightEuc}

instance iMemRightEucToEqMemRightEuc
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : MemRightEuc L Q.lEq C] : EqMemRightEuc L Q C 
:= {eqMemRightEuc := K.memRightEuc}

def eqMemRightEuc 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T] {C : T -> P}
[K : EqMemRightEuc L Q C] {a b c : T} := K.eqMemRightEuc a b c 

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
class MemComm {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T -> T) :=
  (memComm : (a b : T) -> (L |- C a) -> (L |- C b) -> (L |- f a b = f b a))

def memComm {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T}
[K : MemComm L Q C f] {a b : T} := K.memComm a b

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
class MemAssoc {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T -> T) :=
  (memAssoc :  (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- (f (f a b) c) = (f a (f b c))))

def memAssoc {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T}
[K : MemAssoc L Q C f] {a b c : T} := K.memAssoc a b c

--------------------------------------------------------------------------------
-- Function Substitution
-- (a = b) -> (f a = f b)
--------------------------------------------------------------------------------

-- Unconstrained
class EqFunSubst {P : Sort u} {T : Sort v} (L : Logic P) (Q : LEq P T) :=
  (eqFunSubst : (a b : T) -> (f : T -> T) ->
    (L |- a = b) -> (L |- f a = f b))

instance iEqFunSubstToFunSubst 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqFunSubst L Q] : FunSubst L Q.lEq
:= {funSubst := K.eqFunSubst}

instance iFunSubstToEqFunSubst 
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
class EqMemToEqFun {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T) :=
  (eqMemToEqFun : (a b : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- a = b) -> (L |- f a = f b))

instance iEqFunSubstToEqMemToEqFun {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T}
[K : EqFunSubst L Q] : EqMemToEqFun L Q C f
:= {eqMemToEqFun := fun a b _ _  => K.eqFunSubst a b f}

def eqMemToEqFun {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T}
[K : EqMemToEqFun L Q C f] {a b : T} := K.eqMemToEqFun a b

--------------------------------------------------------------------------------
-- Predicate Substitution
-- (a = b) -> (P a -> P b)
--------------------------------------------------------------------------------

class EqPredSubst {P : Sort u} {T : Sort v} (L : Logic P) (Q : LEq P T) :=
  (eqPredSubst : (a b : T) -> (f : T -> P) -> 
    (L |- a = b) -> (L |- f a) -> (L |- f b))

instance iEqPredSubstToPredSubst 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : LEq P T]
[K : EqPredSubst L Q] : PredSubst L Q.lEq
:= {predSubst := K.eqPredSubst}

instance iPredSubstToEqPredSubst
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

class EqMemMagLeft {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T -> T)  :=
  (eqMemMagLeft : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- a = b) -> (L |- f c a = f c b))

def eqMemMagLeft {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T}
[K : EqMemMagLeft L Q C f] {a b c : T} := K.eqMemMagLeft a b c

def eqMemMagLeft' {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T} 
[K : EqMemMagLeft L Q C f] {c a b : T} 
(Nc : L |- C c) (Na : L |- C a) (Nb : L|- C b) 
:= K.eqMemMagLeft a b c Na Nb Nc

-- Right Addition / Left Substitution
-- (a = b) -> (f a c = f b c)

class EqMemMagRight {P : Sort u} {T : Sort v}
  (L : Logic P) (Q : LEq P T) (C : T -> P) (f : T -> T -> T)  :=
  (eqMemMagRight : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- a = b) -> (L |- f a c = f b c))

def eqMemMagRight {P : Sort u} {T : Sort v}
{L : Logic P} [Q : LEq P T] {C : T -> P} {f : T -> T -> T}
[K : EqMemMagRight L Q C f] {a b c : T} := K.eqMemMagRight a b c

def eqMemMagRight' {P : Sort u} {T : Sort v} 
{L : Logic P}  [Q : LEq P T] {C : T -> P} {f : T -> T -> T} 
[K : EqMemMagRight L Q C f] {c a b : T} 
(Nc : L |- C c) (Na : L |- C a) (Nb : L|- C b) 
:= K.eqMemMagRight a b c Na Nb Nc
  
end Gaea.Logic
