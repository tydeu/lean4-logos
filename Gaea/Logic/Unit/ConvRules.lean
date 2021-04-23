import Gaea.Logic.Unit.Rules

universes u
variable {P : Sort u}

namespace Gaea

--------------------------------------------------------------------------------
-- Prod/PProd/And
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

-- And p q -> (|- p /\ q)

class ImportAnd (L : Logic.{u,0} P) (F : Binar P) := 
  toFun : (p q : P) -> ((L |- p) /\ (L |- q)) -> (L |- F p q)

abbrev importAnd {L : Logic.{u,0} P} {F} 
  [K : ImportAnd L F] {p q} := K.toFun p q

instance iConjoinOfAnd {L : Logic P} {F} 
  [K : ImportAnd L F] : Conjoin L F := 
  {toFun := fun p q Lp Lq => K.toFun p q (And.intro Lp Lq)}

instance iImportAndOfConjoin {L : Logic P} {F} 
  [K : Conjoin L F] : ImportAnd L F := 
  {toFun := fun p q Apq => K.toFun p q Apq.left Apq.right}

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

-- (|- p /\ q) -> And p q

class ExportAnd (L : Logic.{u,0} P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> And (L |- p) (L |- q)

abbrev exportAnd {L : Logic.{u,0} P} {F} 
  [K : ExportAnd L F] {p q} := K.toFun p q

instance iExportAndOfLeftRight {L : Logic P} {F}
  [CjL : LeftSimp L F] [CjR : RightSimp L F] : ExportAnd L F := 
  {toFun := fun p q LpCq => And.intro (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportAnd {L : Logic P} {F}
  [K : ExportAnd L F] : LeftSimp L F := 
  {toFun := fun p q LpCq => And.left (K.toFun p q LpCq)}

instance iRightSimpOfExportAnd {L : Logic P} {F}
  [K : ExportAnd L F] : RightSimp L F := 
  {toFun := fun p q LpCq => And.right (K.toFun p q LpCq)}

--------------------------------------------------------------------------------
-- Sum/PSum/Or
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

-- Or p q -> (|- p \/ q) 

class ImportOr (L : Logic.{u,0} P) (F : Binar P) := 
  toFun : (p q : P) -> ((L |- p) \/ (L |- q)) -> (L |- F p q)

abbrev importOr {L : Logic.{u,0} P} {F} 
  [K : ImportOr L F] {p q} := K.toFun p q

instance iImportOrOfLeftRightTaut {L : Logic P} {F} 
  [DiL : LeftTaut L F] [DiR : RightTaut L F] : ImportOr L F := 
  {toFun := fun p q Spq => match Spq with 
    | Or.inl Lp => leftTaut Lp | Or.inr Lq => rightTaut Lq}

instance iLeftTautOfImportOr {L : Logic P} {F} 
  [K : ImportOr L F] : LeftTaut L F := 
  {toFun := fun p q Lp => K.toFun p q (Or.inl Lp)}

instance iRightTautOfImportOr {L : Logic P} {F} 
  [K : ImportOr L F] : RightTaut L F := 
  {toFun := fun p q Lq => K.toFun p q (Or.inr Lq)}

-- (|- p \/ q) -> Sum p q 

class ExportSum (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> Sum (L |- p) (L |- q)

abbrev exportSum {L : Logic P} {F} 
  [K : ExportSum L F] {p q} := K.toFun p q

instance iExportSumOfByEither {L : Logic P} {F} 
  [K : ByEither L F] : ExportSum L F := 
  {toFun := fun p q LpDq => K.toFun _ p q LpDq Sum.inl Sum.inr}

instance iByEitherOfExportSum {L : Logic P} {F} 
  [K : ExportSum L F] : ByEither L F := 
  {toFun := fun a p q LpDq fpa fqa => match K.toFun p q LpDq with
    | Sum.inl Lp => fpa Lp | Sum.inr Lq => fqa Lq}

-- (|- p \/ q) -> PSum p q 

class ExportPSum (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> PSum (L |- p) (L |- q)

abbrev exportPSum {L : Logic P} {F} 
  [K : ExportPSum L F] {p q} := K.toFun p q

instance iExportPSumOfByEither {L : Logic P} {F} 
  [K : ByEither L F] : ExportPSum L F := 
  {toFun := fun p q LpDq => K.toFun _ p q LpDq PSum.inl PSum.inr}

instance iByEitherOfExportPSum {L : Logic P} {F} 
  [K : ExportPSum L F] : ByEither L F := 
  {toFun := fun a p q LpDq fpa fqa => match K.toFun p q LpDq with
    | PSum.inl Lp => fpa Lp | PSum.inr Lq => fqa Lq}

-- (|- p \/ q) -> Or p q 

class ExportOr (L : Logic.{u,0} P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> Or (L |- p) (L |- q)

abbrev exportOr {L : Logic.{u,0} P} {F} 
  [K : ExportOr L F] {p q} := K.toFun p q

instance iExportOrOfByEither {L : Logic P} {F} 
  [K : ByEither L F] : ExportOr L F := 
  {toFun := fun p q LpDq => K.toFun _ p q LpDq Or.inl Or.inr}

instance iByEitherOfExportOr {L : Logic P} {F} 
  [K : ExportOr L F] : ByEither L F := 
  {toFun := fun (a : Sort 0) p q LpDq fpa fqa => match K.toFun p q LpDq with
    | Or.inl Lp => fpa Lp | Or.inr Lq => fqa Lq}

