import Gaea.Logic.Dual.Rules

universes u
variable {P : Sort u}

namespace Gaea

--------------------------------------------------------------------------------
-- False
--------------------------------------------------------------------------------

-- False -> (|- falsum)

class funtype ImportFalse (L : Logic P) (falsum : P) 
  => False -> (L |- falsum) 

abbrev importFalse {L : Logic P} {falsum}
  [K : ImportFalse L falsum] := K.toFun

instance iImportFalse {L : Logic P} {p} 
  : ImportFalse L p := pack False.elim

-- (|- falsum) -> False

class funtype ExportFalse (L : Logic P) (falsum : P) 
  => (L |- falsum) -> False

abbrev exportFalse {L : Logic P} {falsum}
  [K : ExportFalse L falsum] := K.toFun

instance iExFalsumOfExportFalse {L : Logic P} {falsum}
  [K : ExportFalse L falsum] : ExFalsum L falsum 
  := pack fun p Lf => False.elim (K.toFun Lf)

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

-- Not p -> (|- ~p)

class funtype ImportNot (L : Logic.{u,0} P) (lneg : Unar P) 
  : {p : P} => Not (L |- p) -> (L |- lneg p) 

abbrev importNot {L : Logic.{u,0} P} {lneg}
  [K : ImportNot L lneg] {p} := K.toFun p

instance iImportNotOfAdFalso {L : Logic.{u,0} P} {lneg} 
  [K : ImportNot L lneg] : AdFalso L lneg := repack K

instance iAdFalsoOfImportNot {L : Logic.{u,0} P} {lneg} 
  [K : AdFalso L lneg] : ImportNot L lneg := repack K

-- (|- ~p) -> Not p

class funtype ExportNot (L : Logic.{u,0} P) (lneg : Unar P) 
  : {p : P} => (L |- lneg p) -> Not (L |- p) 

abbrev exportNot {L : Logic.{u,0} P} {lneg}
  [K : ExportNot L lneg] {p} := K.toFun p

instance iExportNotOfNoncontradiction {L : Logic.{u,0} P} {lneg} 
  [K : ExportNot L lneg] : Noncontradiction L lneg := repack K

instance iNoncontradictionOfExportNot {L : Logic.{u,0} P} {lneg} 
  [K : Noncontradiction L lneg] : ExportNot L lneg := repack K
