import Gaea.Logic.Quant.Type

universes u v

namespace Gaea.Logic

class LForall (P : Sort u) (T : Sort v) :=
  (lForall : Quant P T)

namespace LForall
abbrev Forall {P : Sort u} {T : Sort v} (K : LForall P T) := K.lForall
end LForall

class LExists (P : Sort u) (T : Sort v) :=
  (lExists : Quant P T)

namespace LExists
abbrev Exists {P : Sort u} {T : Sort v} (K : LExists P T) := K.lExists
end LExists

end Gaea.Logic
