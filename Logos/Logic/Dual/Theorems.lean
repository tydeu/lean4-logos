import Logos.Logic.Rel.Rules
import Logos.Logic.Fun.Rules
import Logos.Logic.Unit.Rules
import Logos.Logic.Dual.Rules
import Logos.Logic.Unit.Tactics
import Logos.Logic.Dual.Tactics

universe u
variable {P : Sort u}

namespace Logos

open Tactics

variable 
  {L : Logic P} {F : Binar P} {f : Unar P}

--------------------------------------------------------------------------------
-- Contraposition
--------------------------------------------------------------------------------

-- ((|- ~q) -> (|- ~p)) -> (|- p -> q)

def byContrapositionByDneImpContra 
(DnE : DoubleElim L f)
(Cnd : Condition L F)
(ByC : ByContradiction L f)
: (p q : P) -> ((L |- f q) -> (L |- f p)) -> (L |- F p q)
:= by
  intro p q 
  assume LNq_to_LNp
  condition Lp
  apply doubleElim (f := f)
  byContradiction LNq
  have LNp := LNq_to_LNp LNq
  contradiction LNp Lp

instance iByContrapositionByDneImpContra 
[DnE : DoubleElim L f]
[Cnd : Condition L F]
[ByC : ByContradiction L f]
: ByContraposition L F f := pack $ 
  byContrapositionByDneImpContra DnE Cnd ByC

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

-- (|- p -> q) -> (|- ~q) -> (|- ~p) 

def mtByMpContra
(Mp  : ModusPonens L F) 
(ByC : ByContradiction L f)
: (p q : P) -> (L |- F p q) -> (L |- f q) -> (L |- f p)
:= by
  intro p q 
  assume LpTq LNq
  byContradiction Lp
  have Lq := mp LpTq Lp
  contradiction LNq Lq

instance iModusTollensByMpContra 
[Mp  : ModusPonens L F] [ByC : ByContradiction L f]
: ModusTollens L F f := pack $ mtByMpContra Mp ByC

--------------------------------------------------------------------------------
-- By Contradiction
--------------------------------------------------------------------------------

def byContraByAdFalsoNoncontra
(AdF : AdFalso L f) 
(Nc  : Noncontradiction L f)
: (p : P) -> ((L |- p) -> Contradiction L f) -> (L |- f p)
:= by
  intro p LpC
  adFalso Lp
  have C := (LpC Lp).2
  noncontradiction C.1 C.2

instance iByContraByAdFalsoNoncontra
[AdF : AdFalso L f] [Nc : Noncontradiction L f] 
: ByContradiction L f := pack $ byContraByAdFalsoNoncontra AdF Nc
