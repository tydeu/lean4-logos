import Gaea.Logic.Judgment
import Gaea.Logic.Quant.Type

universes u v w
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Universial Quantification
--------------------------------------------------------------------------------

class UnivGen (L : Logic P) (U : Quant P T) := 
  ug : (f : T -> P) -> ((a : T) -> (L |- f a)) -> (L |- U f)

def ug {L : Logic P} {U : Quant P T} 
  [K : UnivGen L U] {f} := K.ug f

class UnivInst (L : Logic P) (U : Quant P T) := 
  ui : (f : T -> P) -> (L |- U f) -> ((a : T) -> (L |- f a))  

def ui {L : Logic P} {U : Quant P T} 
  [K : UnivInst L U] {f} := K.ui f

--------------------------------------------------------------------------------
-- Existential Quantification
--------------------------------------------------------------------------------

class ExstGen (L : Logic P) (X : Quant P T) := 
  xg : (f : T -> P) -> (a : T) -> (L |- f a) -> (L |- X f)

def xg {L : Logic P} {X : Quant P T}  
  [K : ExstGen L X] {f} := K.xg f

class ExstInst (L : Logic P) (X : Quant P T) := 
  xi : (r : Sort w) -> (f : T -> P) ->  (L |- X f) -> 
    ((a : T) -> (L |- f a) -> r) -> r

def xi {L : Logic P} {X : Quant P T} 
  [K : ExstInst L X] {r f} := K.xi r f

end Gaea.Logic