import Gaea.Logic.Rel.Type

universes u v

namespace Gaea.Logic 

class SEq (P : Sort u) (T : Sort v) :=
  eq : Rel P T

abbrev eq {P : Sort u} {T : Sort v} [K : SEq P T] := K.eq

end Gaea.Logic
