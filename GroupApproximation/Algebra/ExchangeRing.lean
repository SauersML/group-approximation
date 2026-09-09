import GroupApproximation.Algebra.PurelyInfiniteSandwich
import GroupApproximation.Leavitt.ExchangeRefinement
import GroupApproximation.Meta.AxiomGuard

/-!
# Exchange rings, and Ara's theorem that purely infinite simple rings are exchange

`non_mf_groups_exist.tex`, proof of Theorem `thm:headline` (line 1133):

> The ring `R` is purely infinite simple~\cite{AbramsAranda} and therefore an
> exchange ring~\cite{AraExchange}, so by Preusser's sandwich
> theorem~\cite[Theorem~3]{Preusser} there is an ideal `I` of `R` with
> `EL_4(R,I) ≤ N ≤ C_4(R,I)`.

This module carries the middle clause, at the generality the sentence states
it: **every** purely infinite simple ring is an exchange ring, with no
countability, no algebra structure, and no restriction to Leavitt algebras.
The citation is P. Ara, *Extensions of exchange rings*, J. Algebra **197**
(1997), 409--423, and the fact for purely infinite simple rings.

## The definition

Mathlib has no exchange-ring API, so `IsExchangeRing` is defined here in
Nicholson's element-wise form (W. K. Nicholson, *Lifting idempotents and
exchange rings*, Trans. AMS **229** (1977), 269--278, Theorem 2.1): for every
`x` there is an idempotent `e ∈ xR` with `1 - e ∈ (1-x)R`.  For a unital ring
that is equivalent to Crawley--Jónsson--Warfield's exchange property for the
module `R_R`, and it is the form every step of Preusser's argument consumes.

It is definitionally the predicate the tree already carries under the name
`ExchangePrerequisite.HasRightExchange`; `isExchangeRing_iff_hasRightExchange`
records that, so nothing below is a competing definition.

## Ara's theorem, and why it is short here

The two halves were both already in the tree and had never been composed:

* `MFQuotientUnits.exists_sandwich_of_isPurelyInfiniteSimpleRing`
  (`Algebra/PurelyInfiniteSandwich.lean`) takes the printed
  Ara--Goodearl--Pardo idempotent form of pure infiniteness to the sandwich
  clause `∀ a ≠ 0, ∃ x y, x * a * y = 1`;
* `ExchangePrerequisite.hasRightExchange_of_singleSandwich`
  (`Leavitt/ExchangePrerequisite.lean`) is Ara's own construction of the
  Nicholson idempotent from a sandwich witness, for an arbitrary nontrivial
  unital ring.

Nontriviality is free: a purely infinite simple ring is simple, and Mathlib's
`IsSimpleRing.instNontrivial` supplies `Nontrivial R`.

So `isExchangeRing_of_isPurelyInfiniteSimpleRing` needs no hypothesis at all
beyond the printed one, and in particular no countability and no
Ara--Goodearl--Pardo §1 comparison theory.

## What is exported downstream

`IsExchangeRing.hasFiniteRightExchangePartitions` converts the definition into
the finite orthogonal refinement that Preusser's Proposition 21 actually uses,
through `ExchangeRefinement.hasFiniteRightExchangePartitions_of_hasRightExchange`.
That is the interface `Algebra/PreusserSandwichExchange.lean` consumes in order
to state Preusser's Theorem 3 with the printed hypothesis "exchange ring".
-/

namespace GroupApproximation

variable {R : Type*} [Ring R]

/-! ### Nicholson's element-wise definition -/

/-- **An exchange ring**, in Nicholson's element-wise form: for every `x` there
is an idempotent `e` in the principal right ideal `xR` whose complement `1 - e`
lies in `(1 - x)R`.

For a unital ring this is equivalent to the exchange property of the module
`R_R` (Nicholson, Theorem 2.1), and it is the property Preusser's argument
consumes. -/
def IsExchangeRing (R : Type*) [Ring R] : Prop :=
  ∀ x : R, ∃ e : R, IsIdempotentElem e ∧ (∃ r : R, e = x * r) ∧
    ∃ s : R, 1 - e = (1 - x) * s

namespace IsExchangeRing

/-- The witness, unpacked at a single element. -/
theorem exists_idempotent (h : IsExchangeRing R) (x : R) :
    ∃ e r s : R, IsIdempotentElem e ∧ e = x * r ∧ 1 - e = (1 - x) * s := by
  obtain ⟨e, he, ⟨r, hr⟩, ⟨s, hs⟩⟩ := h x
  exact ⟨e, r, s, he, hr, hs⟩

end IsExchangeRing

/-! ### Agreement with the predicate already in the tree -/

/-- `IsExchangeRing` is the tree's `ExchangePrerequisite.HasRightExchange`, with
the existential quantifiers regrouped so that the printed phrase "an idempotent
in `xR` with `1 - e ∈ (1-x)R`" can be read off the statement. -/
theorem isExchangeRing_iff_hasRightExchange :
    IsExchangeRing R ↔ ExchangePrerequisite.HasRightExchange R := by
  constructor
  · intro h x
    obtain ⟨e, r, s, he, hr, hs⟩ := h.exists_idempotent x
    exact ⟨e, r, s, he, hr, hs⟩
  · intro h x
    obtain ⟨e, r, s, he, hr, hs⟩ := h x
    exact ⟨e, he, ⟨r, hr⟩, ⟨s, hs⟩⟩

theorem IsExchangeRing.hasRightExchange (h : IsExchangeRing R) :
    ExchangePrerequisite.HasRightExchange R :=
  isExchangeRing_iff_hasRightExchange.mp h

theorem ExchangePrerequisite.HasRightExchange.isExchangeRing
    (h : ExchangePrerequisite.HasRightExchange R) : IsExchangeRing R :=
  isExchangeRing_iff_hasRightExchange.mpr h

/-- The finite orthogonal refinement of a decomposition of `1`, which is the
form Preusser's Proposition 21 consumes. -/
theorem IsExchangeRing.hasFiniteRightExchangePartitions (h : IsExchangeRing R) :
    ExchangePrerequisite.HasFiniteRightExchangePartitions R :=
  ExchangePrerequisite.hasFiniteRightExchangePartitions_of_hasRightExchange
    h.hasRightExchange

/-- Conversely the finite refinement contains the one-element property, so the
two interfaces are equivalent and no strength is lost by passing through
`IsExchangeRing`. -/
theorem isExchangeRing_of_hasFiniteRightExchangePartitions
    (h : ExchangePrerequisite.HasFiniteRightExchangePartitions R) :
    IsExchangeRing R :=
  (ExchangePrerequisite.hasRightExchange_of_finitePartitions h).isExchangeRing

/-! ### Ara's theorem -/

/-- Single-sandwich division makes a nontrivial unital ring an exchange ring.
This is Ara's construction, already carried in the tree in the Nicholson
orientation. -/
theorem isExchangeRing_of_singleSandwich [Nontrivial R]
    (hdiv : HasSingleSandwichDivision R) : IsExchangeRing R :=
  (ExchangePrerequisite.hasRightExchange_of_singleSandwich hdiv).isExchangeRing

/-- **Ara's theorem: every purely infinite simple ring is an exchange ring.**

`IsPurelyInfiniteSimpleRing` is the printed Ara--Goodearl--Pardo idempotent
form (Definitions 1.2): simple, and every nonzero `a` has an infinite
idempotent inside `aR`.  No further hypothesis is used. -/
theorem isExchangeRing_of_isPurelyInfiniteSimpleRing
    (hR : MFQuotientUnits.IsPurelyInfiniteSimpleRing R) : IsExchangeRing R := by
  haveI : IsSimpleRing R := hR.isSimpleRing
  refine isExchangeRing_of_singleSandwich ?_
  intro a ha
  exact MFQuotientUnits.exists_sandwich_of_isPurelyInfiniteSimpleRing hR ha

/-! ### The printed sentence

The clause carried here is the second of the three in the sentence at
`non_mf_groups_exist.tex` line 1133; the first is
`AryLeavitt.isPurelyInfiniteSimpleRing` and the third is Preusser's Theorem 3.
The statement is packaged as a closed `Prop` so that it can be audited: a
theorem carrying `R` and the pure-infiniteness hypothesis in front of the colon
is conditional however clean its proof is. -/

/-- **Printed:** "The ring `R` is purely infinite simple and therefore an
exchange ring." -/
def PurelyInfiniteSimpleIsExchange : Prop :=
  ∀ (R : Type) [Ring R],
    MFQuotientUnits.IsPurelyInfiniteSimpleRing R → IsExchangeRing R

/-- Closed proof of the printed implication, for every purely infinite simple
unital ring. -/
theorem manuscriptSentence_purelyInfiniteSimpleIsExchange :
    PurelyInfiniteSimpleIsExchange := by
  intro R _ hR
  exact isExchangeRing_of_isPurelyInfiniteSimpleRing hR

end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.isExchangeRing_of_isPurelyInfiniteSimpleRing
#audit_closed_axioms
  GroupApproximation.manuscriptSentence_purelyInfiniteSimpleIsExchange
