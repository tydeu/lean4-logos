import Logos.Logic.Unit.Rules

universes u
variable {P : Sort u}

namespace Logos

--------------------------------------------------------------------------------
-- Prod/PProd
--------------------------------------------------------------------------------

-- Prod p q -> (|- F p q)

class ImportProd (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> Prod (L |- p) (L |- q) -> (L |- F p q)

abbrev importProd {L : Logic P} {F} 
  [K : ImportProd L F] {p q} := K.toFun p q

instance iConjoinOfImportProd {L : Logic P} {F} 
  [K : ImportProd L F] : Conjoin L F := 
  {toFun := fun p q Lp Lq => K.toFun p q (Prod.mk Lp Lq)}

instance iImportProdOfConjoin {L : Logic P} {F} 
  [K : Conjoin L F] : ImportProd L F := 
  {toFun := fun p q Ppq => K.toFun p q Ppq.fst Ppq.snd}

-- PProd p q -> (|- p /\ q)

class ImportPProd (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> PProd (L |- p) (L |- q) -> (L |- F p q)

abbrev importPProd {L : Logic P} {F} 
  [K : ImportPProd L F] {p q} := K.toFun p q

instance iConjoinOfImportPProd {L : Logic P} {F} 
  [K : ImportPProd L F] : Conjoin L F := 
  {toFun := fun p q Lp Lq => K.toFun p q (PProd.mk Lp Lq)}

instance iImportPProdOfConjoin {L : Logic P} {F} 
  [K : Conjoin L F] : ImportPProd L F := 
  {toFun := fun p q Ppq => K.toFun p q Ppq.fst Ppq.snd}

instance iImportProdOfImportPProd {L : Logic P} {F} 
  [K : ImportPProd L F] : ImportProd L F := 
  {toFun := fun p q Ppq => K.toFun p q (PProd.mk (Ppq.fst) (Ppq.snd))}

-- (|- p /\ q) -> Prod p q

class ExportProd (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> Prod (L |- p) (L |- q)

abbrev exportProd {L : Logic P} {F} 
  [K : ExportProd L F] {p q} := K.toFun p q

instance iExportProdOfLeftRight {L : Logic P} {F}
  [CjL : LeftSimp L F] [CjR : RightSimp L F] : ExportProd L F := 
  {toFun := fun p q LpCq => Prod.mk (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportProd {L : Logic P} {F}
  [K : ExportProd L F] : LeftSimp L F := 
  {toFun := fun p q LpCq => Prod.fst (K.toFun p q LpCq)}

instance iRightSimpOfExportProd {L : Logic P} {F}
  [K : ExportProd L F] : RightSimp L F := 
  {toFun := fun p q LpCq => Prod.snd (K.toFun p q LpCq)}

-- (|- p /\ q) -> PProd p q

class ExportPProd (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> PProd (L |- p) (L |- q)

abbrev exportPProd {L : Logic P} {F} 
  [K : ExportPProd L F] {p q} := K.toFun p q

instance iExportPProdOfLeftRight {L : Logic P} {F}
  [CjL : LeftSimp L F] [CjR : RightSimp L F] : ExportPProd L F := 
  {toFun := fun p q LpCq => PProd.mk (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportPProd {L : Logic P} {F}
  [K : ExportPProd L F] : LeftSimp L F := 
  {toFun := fun p q LpCq => PProd.fst (K.toFun p q LpCq)}

instance iRightSimpOfExportPProd {L : Logic P} {F}
  [K : ExportPProd L F] : RightSimp L F := 
  {toFun := fun p q LpCq => PProd.snd (K.toFun p q LpCq)}

instance iExportProdOfPProd {L : Logic P} {F}
  [K : ExportPProd L F] : ExportProd L F := 
  {toFun := fun p q LpCq => Prod.mk (leftSimp LpCq) (rightSimp LpCq)}

--------------------------------------------------------------------------------
-- Sum/PSum
--------------------------------------------------------------------------------

-- Sum p q -> (|- p \/ q)

class ImportSum (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> Sum (L |- p) (L |- q) -> (L |- F p q)

abbrev importSum {L : Logic P} {F} 
  [K : ImportSum L F] {p q} := K.toFun p q

instance iImportSumOfLeftRightTaut {L : Logic P} {F} 
  [DiL : LeftTaut L F] [DiR : RightTaut L F] : ImportSum L F := 
  {toFun := fun p q Spq => match Spq with 
    | Sum.inl Lp => leftTaut Lp | Sum.inr Lq => rightTaut Lq}

instance iLeftTautOfImportSum {L : Logic P} {F} 
  [K : ImportSum L F] : LeftTaut L F := 
  {toFun := fun p q Lp => K.toFun p q (Sum.inl Lp)}

instance iRightTautOfImportSum {L : Logic P} {F} 
  [K : ImportSum L F] : RightTaut L F := 
  {toFun := fun p q Lq => K.toFun p q (Sum.inr Lq)}

-- PSum p q -> (|- p \/ q) 

class ImportPSum (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> PSum (L |- p) (L |- q) -> (L |- F p q)

abbrev importPSum {L : Logic P} {F} 
  [K : ImportPSum L F] {p q} := K.toFun p q

instance iImportPSumOfLeftRightTaut {L : Logic P} {F} 
  [DiL : LeftTaut L F] [DiR : RightTaut L F] : ImportPSum L F := 
  {toFun := fun p q Spq => match Spq with 
    | PSum.inl Lp => leftTaut Lp | PSum.inr Lq => rightTaut Lq}

instance iLeftTautOfImportPSum {L : Logic P} {F} 
  [K : ImportPSum L F] : LeftTaut L F := 
  {toFun := fun p q Lp => K.toFun p q (PSum.inl Lp)}

instance iRightTautOfImportPSum {L : Logic P} {F} 
  [K : ImportPSum L F] : RightTaut L F := 
  {toFun := fun p q Lq => K.toFun p q (PSum.inr Lq)}

-- (|- p \/ q) -> Sum p q 

class ExportSum (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> Sum (L |- p) (L |- q)

abbrev exportSum {L : Logic P} {F} 
  [K : ExportSum L F] {p q} := K.toFun p q

instance iExportSumOfByEither {L : Logic P} {F} 
  [K : ByEither L F] : ExportSum L F := 
  {toFun := fun p q LpDq => K.toFun p q LpDq _ Sum.inl Sum.inr}

instance iByEitherOfExportSum {L : Logic P} {F} 
  [K : ExportSum L F] : ByEither L F := 
  {toFun := fun p q LpDq r fpr fqr => match K.toFun p q LpDq with
    | Sum.inl Lp => fpr Lp | Sum.inr Lq => fqr Lq}

-- (|- p \/ q) -> PSum p q 

class ExportPSum (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> PSum (L |- p) (L |- q)

abbrev exportPSum {L : Logic P} {F} 
  [K : ExportPSum L F] {p q} := K.toFun p q

instance iExportPSumOfByEither {L : Logic P} {F} 
  [K : ByEither L F] : ExportPSum L F := 
  {toFun := fun p q LpDq => K.toFun p q LpDq _ PSum.inl PSum.inr}

instance iByEitherOfExportPSum {L : Logic P} {F} 
  [K : ExportPSum L F] : ByEither L F := 
  {toFun := fun p q LpDq r fpr fqr => match K.toFun p q LpDq with
    | PSum.inl Lp => fpr Lp | PSum.inr Lq => fqr Lq}
