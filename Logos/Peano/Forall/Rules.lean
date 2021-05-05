import Logos.Logic.Unit.Rules
import Logos.Logic.Quant.Rules
import Logos.Peano.Forall.Syntax

universes u v
variable {P : Sort u} {T : Sort v}

open Logos.Notation
open Logos.Peano.Notation

namespace Logos.Peano

--------------------------------------------------------------------------------
-- Abstract Rules
--------------------------------------------------------------------------------

class ForallNatIntro (L : Logic P) (N : IsNat P T) (FaN : SForallNat P T) :=
  toFun : (f : T -> P) -> ((a : T) -> (L |- nat a) -> (L |- f a)) -> 
    (L |- forallNat a => f a)

def forallNatIntro  {L : Logic P} [N : IsNat P T] [FaN : SForallNat P T] 
  [K : ForallNatIntro L N FaN] {f} := K.toFun f

class ForallNatElim (L : Logic P) (N : IsNat P T) (FaN : SForallNat P T) := 
  toFun : (f : T -> P) -> (L |- forallNat a => f a) ->
    ((a : T) -> (L |- nat a) -> (L |- f a))

def forallNatElim   {L : Logic P} [N : IsNat P T] [FaN : SForallNat P T] 
  [K : ForallNatElim L N FaN] {f} (p) {a} := K.toFun f p a

--------------------------------------------------------------------------------
-- Forall/IF Implementation Rules
--------------------------------------------------------------------------------

def forallIfNatIntro {L : Logic P} 
[N : IsNat P T] [Fa : SForall P T] [larr : LArr P]
[Ug : UnivGen L Fa.toFun] [C : Condition L larr.toFun]
{f : T -> P} (F : (a : T) -> (L |- nat a) -> (L |- f a))
: L |- forall a => nat a -> f a
:= ug fun a => condition fun Na => F a Na

def LForallIfNatIntro {L : Logic P} 
(N : IsNat P T) [Fa : SForall P T] [larr : LArr P] 
(Ug : UnivGen L Fa.toFun) (C : Condition L larr.toFun) 
: ForallNatIntro L N (LForallIfNat N Fa larr)
:= {toFun := fun _ F => forallIfNatIntro F}

instance iForallIfNatIntro {L : Logic P} 
[N : IsNat P T] [Fa : SForall P T] [larr : LArr P]
[Ug : UnivGen L Fa.toFun] [C : Condition L larr.toFun]
: ForallNatIntro L N (LForallIfNat N Fa larr)
:= LForallIfNatIntro N Ug C

def forallIfNatElim {L : Logic P} 
[N : IsNat P T] [Fa : SForall P T] [larr : LArr P]
[Ui : UnivInst L Fa.toFun] [Mp : ModusPonens L larr.toFun]
{f : T -> P} (p : L |- forall (a : T) => nat a -> f a) 
{a : T} (Na : L |- nat a) : L |- f a
:= mp (ui p a) Na

def LForallIfNatElim {L : Logic P} 
(N : IsNat P T) [Fa : SForall P T] [larr : LArr P]
(Ui : UnivInst L Fa.toFun) (Mp : ModusPonens L larr.toFun) 
: ForallNatElim L N (LForallIfNat N Fa larr)
:= {toFun := fun _ p a Na => forallIfNatElim p Na}

instance iForallIfNatElim {L : Logic P} 
[N : IsNat P T] [Fa : SForall P T] [larr : LArr P]
[Ui : UnivInst L Fa.toFun] [Mp : ModusPonens L larr.toFun]
: ForallNatElim L N (LForallIfNat N Fa larr)
:= LForallIfNatElim N Ui Mp
