import Gaea.Logic.Basic.Rules
import Gaea.Peano.Forall.Notation

universes u v

open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Abstract Rules
--------------------------------------------------------------------------------

class ForallNatIntro {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (FaN : ForallNat P T) :=
  (forallNatIntro : (f : T -> P) -> ((a : T) -> (L |- nat a) -> (L |- f a)) -> 
    (L |- forallNat a => f a))

def forallNatIntro {P : Sort u} {T : Sort v}
  {L : Logic P} [N : IsNat P T] [FaN : ForallNat P T] 
  [K : ForallNatIntro L N FaN] {f : T -> P} := K.forallNatIntro f

class ForallNatElim {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (FaN : ForallNat P T) := 
  (forallNatElim : (f : T -> P) -> (L |- forallNat a => f a) ->
    ((a : T) -> (L |- nat a) -> (L |- f a)))

def forallNatElim {P : Sort u} {T : Sort v}
  {L : Logic P} [N : IsNat P T] [FaN : ForallNat P T] 
  [K : ForallNatElim L N FaN] {f : T -> P} (p : L |- forallNat a => f a)
  {a : T} := K.forallNatElim f p a

--------------------------------------------------------------------------------
-- Forall/If Implementation Rules
--------------------------------------------------------------------------------

def forallIfNatIntro {P : Sort u} {T : Sort v} {L : Logic P} 
  [N : IsNat P T] [Fa : LForall P T] [If : LIf P] [ForallIntro L Fa] [IfIntro L If]
  {f : T -> P} (F : (a : T) -> (L |- nat a) -> (L |- f a))
  : L |- forall a => nat a -> f a
  := forallIntro fun a => ifIntro fun Na => F a Na

def LForallIfNatIntro {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Fa : LForall P T) (If : LIf P) 
  (FaI : ForallIntro L Fa) (IfI : IfIntro L If) 
  : ForallNatIntro L N (LForallIfNat N Fa If)
  := {forallNatIntro := fun _ F => forallIfNatIntro F}

instance iForallIfNatIntro {P : Sort u} {T : Sort v} {L : Logic P} 
  [N : IsNat P T] [Fa : LForall P T] [If : LIf P] 
  [FaI : ForallIntro L Fa] [IfI : IfIntro L If]
  : ForallNatIntro L N (LForallIfNat N Fa If)
  := {forallNatIntro := (LForallIfNatIntro L N Fa If FaI IfI).forallNatIntro}

def forallIfNatElim {P : Sort u} {T : Sort v} {L : Logic P} 
  [N : IsNat P T] [Fa : LForall P T] [If : LIf P] [ForallElim L Fa] [IfElim L If]
  {f : T -> P} (p : L |- forall (a : T) => nat a -> f a) 
  {a : T} (Na : L |- nat a) : L |- f a
  := ifElim (forallElim p a) Na

def LForallIfNatElim {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Fa : LForall P T) (If : LIf P) 
  (FaE : ForallElim L Fa) (IfE : IfElim L If) 
  : ForallNatElim L N (LForallIfNat N Fa If)
  := {forallNatElim := fun _ p a Na => forallIfNatElim p Na}

instance iForallIfNatElim {P : Sort u} {T : Sort v} {L : Logic P} 
  [N : IsNat P T] [Fa : LForall P T] [If : LIf P] 
  [FaE : ForallElim L Fa] [IfE : IfElim L If]
  : ForallNatElim L N (LForallIfNat N Fa If)
  := {forallNatElim := (LForallIfNatElim L N Fa If FaE IfE).forallNatElim}

end Gaea.Peano
