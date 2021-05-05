universes u v w
variable {N : Sort u} {O : Sort v} {T : Sort w}

namespace Gaea

--------------------------------------------------------------------------------
-- Packing
--------------------------------------------------------------------------------

class Pack (N : Sort u) (O : outParam (Sort v)) :=
  apply : O -> N

class Unpack (N : Sort u) (O : outParam (Sort v)) :=
  apply : N -> O

abbrev pack [K : Pack N O] := K.apply 
abbrev unpack [K : Unpack N O] := K.apply
abbrev repack [P : Pack N T] [U : Unpack O T] : O -> N 
  := fun v => pack (unpack v)

--------------------------------------------------------------------------------
-- Newtypes
--------------------------------------------------------------------------------

class Newtype (N : Sort u) (O : outParam (Sort v)) :=
  pack : O -> N 
  unpack : N -> O

namespace Newtype
instance ofPackUnpack [P : Pack N O] [U : Unpack N O] 
  : Newtype N O := {pack := P.apply, unpack := U.apply}
instance toPack [K : Newtype N O] : Pack N O := {apply := K.pack}
instance toUnpack [K : Newtype N O] : Unpack N O := {apply := K.unpack}
end Newtype

class Funtype (N : Sort u) (O : outParam (Sort v)) (T : outParam (Sort w)) 
  extends Newtype N O := (apply : N -> T)

namespace Funtype
instance toCoeFun [K : Funtype N O T] 
  : CoeFun N (fun _ => T) := {coe := apply}
end Funtype

namespace Pack
abbrev toFun (K : Pack N O) := K.apply
abbrev toApplyFun (K : Pack N O) := K.apply
instance isFuntype : Funtype (Pack N O) (O -> N) (O -> N) 
  := {pack := mk, unpack := toFun, apply := toFun}
end Pack

namespace Unpack
abbrev toFun (K : Unpack N O) := K.apply
abbrev toApplyFun (K : Pack N O) := K.apply
instance isFuntype : Funtype (Unpack N O) (N -> O) (N -> O)
  := {pack := mk, unpack := toFun, apply := toFun}
end Unpack
