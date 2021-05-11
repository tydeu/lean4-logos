import Logos.Logic.Dual.Rules

universes u
variable {P : Sort u}

namespace Logos

--------------------------------------------------------------------------------
-- False
--------------------------------------------------------------------------------

-- False -> (|- falsum)

class funtype ImportFalse (L : Logic P) (falsum : P) :
  False -> (L |- falsum) 

abbrev importFalse {L : Logic P} {falsum}
  [K : ImportFalse L falsum] := unpack K

instance iImportFalse {L : Logic P} {p} 
  : ImportFalse L p := pack False.elim

-- (|- falsum) -> False

class funtype ExportFalse (L : Logic P) (falsum : P) :
  (L |- falsum) -> False

abbrev exportFalse {L : Logic P} {falsum}
  [K : ExportFalse L falsum] := unpack K

instance iExFalsumOfExportFalse {L : Logic P} {falsum}
  [K : ExportFalse L falsum] : ExFalsum L falsum 
  := pack fun p Lf => False.elim (unpack K Lf)
