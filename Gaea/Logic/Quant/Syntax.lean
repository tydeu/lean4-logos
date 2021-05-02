import Gaea.Newtype
import Gaea.FunTypes

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea

class funtype SForall (P : Sort u) (T : Sort v) : Quant P T
class funtype SExists (P : Sort u) (T : Sort v) : Quant P T

abbrev lForall [K : SForall P T] := K.toFun
abbrev lExists [K : SExists P T] := K.toFun

namespace Notation

open Lean

scoped macro "∀ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``lForall xs b
scoped macro "forall " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``lForall xs b

scoped macro "∃ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``lExists xs b
scoped macro "exists " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``lExists xs b

@[appUnexpander Gaea.lForall] 
def unexpandLForall : Lean.PrettyPrinter.Unexpander
  | `($_op:ident fun $x:ident => ∀ $xs:binderIdent* => $b)
    => `(∀ $x:ident $xs:binderIdent* => $b)
  | `($_op:ident fun $x:ident => $b)
    => `(∀ $x:ident => $b)
  | `($_op:ident fun ($x:ident : $t) => $b)              
    => `(∀ ($x:ident : $t) => $b)
  | _  => throw ()

@[appUnexpander Gaea.lExists] 
def unexpandLExists : Lean.PrettyPrinter.Unexpander
  | `($_op:ident fun $x:ident => ∃ $xs:binderIdent* => $b)
    => `(∃ $x:ident $xs:binderIdent* => $b)
  | `($_op:ident fun $x:ident => $b)          
    => `(∃ $x:ident => $b)
  | `($_op:ident fun ($x:ident : $t) => $b)
    => `(∃ ($x:ident : $t) => $b)
  | _ => throw ()

