import Gaea.Function

universe u

namespace Gaea.Logic 

-- Constants

class LTrue (P : Sort u) :=
  (true : P)

abbrev true {P : Sort u} [K : LTrue P] := K.true

class LFalse (P : Sort u) :=
  (false : P)

abbrev false {P : Sort u} [K : LFalse P] := K.false

-- Connectives

class Imp (P : Sort u) :=
  (imp : Binar P)

abbrev imp {P : Sort u} [K : Imp P] := K.imp

class LIff (P : Sort u) :=
  (iff : Binar P)

abbrev iff {P : Sort u} [K : LIff P] := K.iff

class Conj (P : Sort u):=
  (conj : Binar P)

abbrev conj {P : Sort u} [K : Conj P] := K.conj

class Disj (P : Sort u) :=
  (disj : Binar P)

abbrev disj {P : Sort u} [K : Disj P] := K.disj

class LNot (P : Sort u) :=
  (not : Unar P)

abbrev lnot {P : Sort u} [K : LNot P] := K.not

end Gaea.Logic