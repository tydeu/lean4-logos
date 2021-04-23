import Gaea.Logic.Rel.Rules
import Gaea.Logic.Fun.Rules
import Gaea.Logic.Unit.Rules
import Gaea.Logic.Dual.Rules
import Gaea.Logic.Unit.Tactics
import Gaea.Logic.Dual.Tactics

universe u
variable {P : Sort u}

namespace Gaea

--------------------------------------------------------------------------------
-- Contraposition
--------------------------------------------------------------------------------

-- ((|- ~q) -> (|- ~p)) -> (|- p -> q)

def byContrapositionByDneImpContra 
{L : Logic P} {F : Binar P} {f : Unar P}
(DnE : DblNegElim L f)
(Cnd : Condition L F)
(ByC : ByContradiction L f)
: (p q : P) -> ((L |- f q) -> (L |- f p)) -> (L |- F p q)
:= by
  intro p q 
  assume LNq_to_LNp
  condition Lp
  apply dblNegElim (f := f)
  byContradiction LNq
  have LNp := LNq_to_LNp LNq
  contradiction LNp Lp

instance iByContrapositionByDneImpContra 
{L : Logic P} {F : Binar P} {f : Unar P}
[DnE : DblNegElim L f]
[Cnd : Condition L F]
[ByC : ByContradiction L f]
: ByContraposition L F f :=
{toFun := byContrapositionByDneImpContra DnE Cnd ByC}

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

-- (|- p -> q) -> (|- ~q) -> (|- ~p) 

def mtByMpContra
{L : Logic P} {F : Binar P} {f : Unar P}
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
{L : Logic P} {F : Binar P} {f : Unar P}
[Mp  : ModusPonens L F]
[ByC : ByContradiction L f]
: ModusTollens L F f :=
{toFun := mtByMpContra Mp ByC}

--------------------------------------------------------------------------------
-- By Contradiction
--------------------------------------------------------------------------------

def byContraByAdFalsoNoncontra
{L : Logic P} {f : Unar P}
(AdF : AdFalso L f) 
(Nc  : Noncontradiction L f)
: (p : P) -> ((L |- p) -> Contradiction L f) -> (L |- f p)
:= by
  intro p LpC
  adFalso Lp
  have C := (LpC Lp).2
  noncontradiction C.1 C.2

instance iByContraByAdFalsoNoncontra {L : Logic P} {f}
[AdF : AdFalso L f] [Nc : Noncontradiction L f] : ByContradiction L f := 
{toFun := byContraByAdFalsoNoncontra AdF Nc}
