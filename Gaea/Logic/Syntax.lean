universes u v

namespace Gaea.Logic 

-- Constants

class True (prop : Sort u) :=
  (true : prop)

export True (true)

class False (prop : Sort u) :=
  (false : prop)

export False (false)

-- Connectives

class If (prop : Sort u) :=
  (if' : prop -> prop -> prop)

export If (if')

class Iff (prop : Sort u) :=
  (iff : prop -> prop -> prop)

export Iff (iff)

class And (prop : Sort u):=
  (and : prop -> prop -> prop)

export And (and)

class Or (prop : Sort u) :=
  (or : prop -> prop -> prop)

export Or (or)

-- Equality

class Eq (prop : Sort u) (form : Sort v) :=
  (eq : form -> form -> prop)

export Eq (eq)

-- Quantifiers

class Forall (prop : Sort u) (form : Sort v) :=
  (forall' : (form -> prop) -> prop)

export Forall (forall')

class Exists (prop : Sort u) (form : Sort v) :=
  (exists' : (form -> prop) -> prop)

export Exists (exists')

end Gaea.Logic
