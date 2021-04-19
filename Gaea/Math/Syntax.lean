import Gaea.Logic.Rel.Type
import Gaea.Logic.Fun.Types

universes u v
variable {P : Sort u} {T : Sort v}

open Gaea.Logic

namespace Gaea.Math

-- Numerics

class Zero (T : Sort u) :=
  zero : T

class One (T : Sort u) :=
  one : T

class Succ (T : Sort u) :=
  toFun : Unar T

namespace Succ
abbrev funType (K : Succ T) := Unar T
instance : CoeFun (Succ T) funType := {coe := fun K => K.toFun}
end Succ

abbrev S [K : Succ T] := K.toFun

-- Operations

class SAdd (T : Sort v) :=
  toFun : Binar T

namespace SAdd
abbrev funType (K : SAdd T) := Binar T
instance : CoeFun (SAdd T) funType := {coe := fun K => K.toFun}
end SAdd

class SMul (T : Sort v) :=
  toFun : Binar T

namespace SMul
abbrev funType (K : SMul T) := Binar T
instance : CoeFun (SMul T) funType := {coe := fun K => K.toFun}
end SMul

-- Inequalities

class SLess (P : Sort u) (T : Sort v) :=
  toFun : Rel P T

namespace SLess
abbrev funType (K : SLess P T) := Rel P T
instance : CoeFun (SLess P T) funType := {coe := fun K => K.toFun}
end SLess

class SLessEq (P : Sort u) (T : Sort v)  :=
  toFun : Rel P T

namespace SLessEq
abbrev funType (K : SLessEq P T) := Rel P T
instance : CoeFun (SLessEq P T) funType := {coe := fun K => K.toFun}
end SLessEq

end Gaea.Math
