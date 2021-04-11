import Gaea.Logic.Prop.Rules
import Gaea.Logic.Quant.Rules
import Gaea.Peano.Forall.Notation

universes u v
variable {P : Sort u} {T : Sort v}

open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Abstract Rules
--------------------------------------------------------------------------------

class ForallNatIntro (L : Logic P) (N : IsNat P T) (FaN : ForallNat P T) :=
  (forallNatIntro : (f : T -> P) -> ((a : T) -> (L |- nat a) -> (L |- f a)) -> 
    (L |- forallNat a => f a))

def forallNatIntro  {L : Logic P} [N : IsNat P T] [FaN : ForallNat P T] 
  [K : ForallNatIntro L N FaN] {f} := K.forallNatIntro f

class ForallNatElim (L : Logic P) (N : IsNat P T) (FaN : ForallNat P T) := 
  (forallNatElim : (f : T -> P) -> (L |- forallNat a => f a) ->
    ((a : T) -> (L |- nat a) -> (L |- f a)))

def forallNatElim   {L : Logic P} [N : IsNat P T] [FaN : ForallNat P T] 
  [K : ForallNatElim L N FaN] {f} (p) {a} := K.forallNatElim f p a

--------------------------------------------------------------------------------
-- Forall/IF Implementation Rules
--------------------------------------------------------------------------------

def forallIfNatIntro {L : Logic P} 
[N : IsNat P T] [Fa : LForall P T] [Im : Imp P]
[Ug : UnivGen L Fa.lForall] [ByI : ByImplication L Im.imp]
{f : T -> P} (F : (a : T) -> (L |- nat a) -> (L |- f a))
: L |- forall a => nat a -> f a
:= ug fun a => byImplication fun Na => F a Na

def LForallIfNatIntro {L : Logic P} 
(N : IsNat P T) [Fa : LForall P T] [Im : Imp P] 
(Ug : UnivGen L Fa.lForall) (ByI : ByImplication L Im.imp) 
: ForallNatIntro L N (LForallIfNat N Fa Im)
:= {forallNatIntro := fun _ F => forallIfNatIntro F}

instance iForallIfNatIntro {L : Logic P} 
[N : IsNat P T] [Fa : LForall P T] [Im : Imp P]
[Ug : UnivGen L Fa.lForall] [ByI : ByImplication L Im.imp]
: ForallNatIntro L N (LForallIfNat N Fa Im)
:= LForallIfNatIntro N Ug ByI

def forallIfNatElim {L : Logic P} 
[N : IsNat P T] [Fa : LForall P T] [Im : Imp P]
[Ui : UnivInst L Fa.lForall] [Mp : ModusPonens L Im.imp]
{f : T -> P} (p : L |- forall (a : T) => nat a -> f a) 
{a : T} (Na : L |- nat a) : L |- f a
:= mp (ui p a) Na

def LForallIfNatElim {L : Logic P} 
(N : IsNat P T) [Fa : LForall P T] [Im : Imp P]
(Ui : UnivInst L Fa.lForall) (Mp : ModusPonens L Im.imp) 
: ForallNatElim L N (LForallIfNat N Fa Im)
:= {forallNatElim := fun _ p a Na => forallIfNatElim p Na}

instance iForallIfNatElim {L : Logic P} 
[N : IsNat P T] [Fa : LForall P T] [Im : Imp P]
[Ui : UnivInst L Fa.lForall] [Mp : ModusPonens L Im.imp]
: ForallNatElim L N (LForallIfNat N Fa Im)
:= LForallIfNatElim N Ui Mp

end Gaea.Peano
