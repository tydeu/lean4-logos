# Gaea

Gaea is a **work-in-progress** metalogic system for Lean 4 **(stable v4.0.0-m2)**.
As a *metalogic* system, Gaea is able to formalize multiple different logics
with varying axiomatic bases and different proof rules.

## Formalization

In Gaea, propositions are simply the inhabitants of some type `P` (a Lean `Sort`).
Thus, the whole type `P` functions as a logical language.

Common logical connectives, like the logical arrow (Unicode `⇒` or ASCII `->`),
are wrapped up in Lean type classes to allow for easy specification.
The class for the arrow is `LArr`. 
Thus, if we wanted to require that the logical language `P` has the logical arrow, 
we simply write `[LArr P]`.

A logic `L` over the propositional language `P` is defined as `L : Logic P`.
Since the language and the logic are separate types, 
we can have multiple logics over the same language.
This way we can analyze the properties of a given language `P` 
under logics with different axioms.

The statement `L ⊢ p` (or ASCII `L |- p`) 
means that proposition `p` holds in logic `L`.
Such a statement is termed a *judgment*.
Implementation-wise, a judgment is a type (a Lean `Sort`) 
and proofs of said judgment are the inhabitants of said type.
Thus, constructing an inhabitant of `L ⊢ p` proves `p` in `L`.

Inference rules (which map between judgments) are then functions between judgments.
For example, the ***modus ponens*** inference rule can be defined as follows:

```lean
(p q : P) -> (L ⊢ p ⇒ q) -> (L ⊢ p) -> (L ⊢ q)
```

And the conditional proof rule can be defined like so:

```lean
(p q : P) -> ((L ⊢ p) -> (L ⊢ q)) -> (L ⊢ p ⇒ q)
```

In proofs with Gaea, inference rules are part of the hypotheses of the proof.
For example, a proof that conditional proof rule for implication entails 
the reflexivity of implication could look like the following:

```lean
def reflByCondition {P : Sort u} (L : Logic P) [LArr P]
(condition : (p q : P) -> ((L ⊢ p) -> (L ⊢ q)) -> (L ⊢ p ⇒ q))
: (p : P) -> (L ⊢ p ⇒ p)
:= by
  intro p
  apply condition p p
  assume Lp
  exact Lp
```

To allow us to automatically infer derivative rules, all rules in Gaea are
wrapped in type classes. 
The class for the conditional proof rule is `Condition`
and the class for reflexivity is `Refl`.
To automatically derive reflexivity from the presence of the conditional proof rule, 
we could construct an instance of `Refl` as follows:

```lean
instance iReflOfCondition {P : Sort u} {L : Logic P} {f : Binar P} 
  [K : Condition L f] : Refl L f := {refl := K.condition p p id}
```

A similar instance, in fact, is already present in Gaea.
Note that, in the above example, we generalized the conditional proof rule to any
`Binar` (binary endofunction), instead of just strictly to implication. 
The definition of said class would thus be something like this:

```lean
class Condition {P : Sort u} (L : Logic P) (f : Binar P) :=
  condition : (p q : P) -> ((L ⊢ p) -> (L ⊢ q)) -> (L ⊢ f p q)
```

Such generalizations are quite common in Gaea, 
and can provide insight as to how many common rules across logic, 
universal algebra, and other maths relate.
For example, as a consequence of this generalization, 
it also makes sense to define the converse of the condition rule, `RightCond`:

```lean
class RightCond {P : Sort u} (L : Logic P) (f : Binar P) :=
  condition : (p q : P) -> ((L ⊢ q) -> (L ⊢ p)) -> (L ⊢ f p q)
```

As such, the original `Condition` rule is just the left variant.
Thus, in Gaea, `Condition` is just an abbreviation for the real class `LeftCond`.

## Organization

The `Gaea.Logic` folder and namespace contain the basic definitions of the metalogic 
along with formalizations of propositional and predicate logic.
The `Unit` subfolder contains definitions for basic propositional logic without negation. 
`Dual` adds negation, `Quant` adds quantifiers, and `Eq` adds equality.

`Gaea.Peano` contains an example formalization in Gaea of the
Peano axioms (as outlined on [Wikipedia](https://en.wikipedia.org/wiki/Peano_axioms))
and some basic proofs about the system.
Those proofs show that Peano addition and multiplication 
form a semiring over the Peano naturals.

**More to come later!**
