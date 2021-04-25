import Gaea.Logic.Judgment
import Gaea.FunTypes

universes u v w
variable {P : Sort u} {T : Sort v}

namespace Gaea

--------------------------------------------------------------------------------
-- Universial Quantification
--------------------------------------------------------------------------------

class UnivGen (L : Logic P) (U : Quant P T) := 
  toFun : (f : T -> P) -> ((a : T) -> (L |- f a)) -> (L |- U f)

def univGen {L : Logic P} {U : Quant P T} 
  [K : UnivGen L U] {f} := K.toFun f

def ug {L : Logic P} {U : Quant P T} 
  [K : UnivGen L U] {f} := K.toFun f

class UnivInst (L : Logic P) (U : Quant P T) := 
  toFun : (f : T -> P) -> (L |- U f) -> ((a : T) -> (L |- f a))  

def univInst {L : Logic P} {U : Quant P T} 
  [K : UnivInst L U] {f} := K.toFun f

def ui {L : Logic P} {U : Quant P T} 
  [K : UnivInst L U] {f} := K.toFun f

--------------------------------------------------------------------------------
-- Existential Quantification
--------------------------------------------------------------------------------

class ExstGen (L : Logic P) (X : Quant P T) := 
  toFun : (f : T -> P) -> (a : T) -> (L |- f a) -> (L |- X f)

def exstGen {L : Logic P} {X : Quant P T}  
  [K : ExstGen L X] {f} := K.toFun f

def xg {L : Logic P} {X : Quant P T}  
  [K : ExstGen L X] {f} := K.toFun f

class ExstInst (L : Logic P) (X : Quant P T) := 
  toFun : (f : T -> P) -> (L |- X f) -> 
    (r : Sort w) -> ((a : T) -> (L |- f a) -> r) -> r

def exstInst {L : Logic P} {X : Quant P T} 
  [K : ExstInst L X] {f} (Xf) {r} := K.toFun f Xf r

def xi {L : Logic P} {X : Quant P T} 
  [K : ExstInst L X] {f} (Xf) {r} := K.toFun f Xf r
