import Logos.Peano.Eq.Rules
import Logos.Logic.Rel.Theorems

open Logos.Notation
namespace Logos.Peano 

--------------------------------------------------------------------------------
-- Derivative Instances
--------------------------------------------------------------------------------

instance iEqNatLeftEucBySymmTransT
{P : Sort u} {T : Sort v} {L : Logic P} [N : PNat P T]
[Q : SEq P T] [QSm : EqNatSymm L N Q] [QTr : EqNatTrans L N Q]
: EqNatLeftEuc L N Q := iEqNatLeftEucOfLeftEucT (K := iLeftEucBySymmTransT)

instance iEqNatJoinBySymmTransT
{P : Sort u} {T : Sort v} {L : Logic P} [N : PNat P T]
[Q : SEq P T] [QSm : EqNatSymm L N Q] [QTr : EqNatTrans L N Q]
: EqNatJoin L N Q := iEqNatJoinOfLeftTransJoinT (K := iLeftTransJoinBySymmTransT)

--------------------------------------------------------------------------------
-- NatEqNat Variations
--------------------------------------------------------------------------------

-- (a = b) /\ (b = c) -> (a = c)

def eqTransNatByNatEq 
{P : Sort u} {T : Sort v} 
{L : Logic P} {N : PNat P T} {Q : SEq P T} 
(QTr : EqNatTrans L N Q) (NQ : NatEqNat L N Q)
: (a b c : T) -> (L |- nat c) -> (L |- a = b) -> (L |- b = c) -> (L |- a = c)
:= by
  intro a b c Nc Qab Qbc
  have Nb := natEq Nc Qbc
  have Na := natEq Nb Qab
  exact eqNatTrans Na Nb Nc Qab Qbc

instance iEqTransNatByNatEq  
{P : Sort u} {T : Sort v} {L : Logic P} 
[N : PNat P T] [Q : SEq P T] [QTr : EqNatTrans L N Q] [NQ : NatEqNat L N Q]
: EqTransNat L N Q := {toFun := eqTransNatByNatEq QTr NQ}

-- (b = a) /\ (c = a) -> (b = c)

def eqLeftEucNatByNatEq 
{P : Sort u} {T : Sort v} 
{L : Logic P} {N : PNat P T} {Q : SEq P T} 
(QEL : EqNatLeftEuc L N Q) (NQ : NatEqNat L N Q)
: (a b c : T) -> (L |- nat a) -> (L |- b = a) -> (L |- c = a) -> (L |- b = c)
:= by
  intro a b c Na Qba Qca
  have Nb := natEq Na Qba
  have Nc := natEq Na Qca
  exact eqNatLeftEuc Na Nb Nc Qba Qca

instance iEqLeftEucNatByNatEq 
{P : Sort u} {T : Sort v} {L : Logic P} 
[N : PNat P T] [Q : SEq P T] [QTr : EqNatLeftEuc L N Q] [NQ : NatEqNat L N Q]
: EqLeftEucNat L N Q := {toFun := eqLeftEucNatByNatEq QTr NQ }

