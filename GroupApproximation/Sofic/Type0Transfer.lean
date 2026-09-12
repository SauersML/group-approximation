import Mathlib.Algebra.Group.Shrink
import Mathlib.Logic.Small.Basic
import GroupApproximation.Sofic.CommensurabilityInvariance

/-!
# Countable groups live in `Type 0`

The proof ledger marks thirty-one steps `MISMATCH` for one reason, recorded
there as `univ0`: the manuscript says "let `H` be a countable group" and the
Lean statement reads `{H : Type}`, so the formal assertion is strictly narrower
than the printed one.  The ledger declines to close the gap by assumption --
"the transfer is true and routine, but it is not in the development, so it may
not be assumed here" -- and it is right to.  This file puts it in the
development.

The transfer is `exists_type0_model`: a countable group in any universe is
isomorphic to a group whose carrier is a `Type`.  Countability gives an
injection into `ℕ`, hence `Small.{0}`; `Shrink.{0}` is then a `Type` carrying a
transported group structure, and `Shrink.mulEquiv` is the isomorphism.

With it, a theorem proved for `Type 0` groups extends to every universe by one
application of the property's isomorphism-invariance, which the development
already has for the properties that matter: `isOperatorMF_of_mulEquiv`,
`isResiduallyFinite_of_mulEquiv`, `HasKazhdanPropertyT.of_mulEquiv`,
`mem_fdUnitaryResidual_mulEquiv`.  `not_isOperatorMF_transfer` is the pattern
written out for the flagship property; the other thirty rows follow it verbatim
with their own invariance lemma.

What this does *not* do is restate the theorems.  Each `Type 0` theorem still
has to be paired with its transfer at the point of use, and until that happens
for a given row the ledger entry stays `MISMATCH` -- correctly.  The obstacle
this file removes is that the transfer did not exist to be applied.
-/

namespace GroupApproximation
namespace Type0Transfer

open CommensurabilityInvariance

universe u

/-- **Countable groups are `Type 0` groups up to isomorphism.**  An injection
into `ℕ` makes the carrier `Small.{0}`, and `Shrink.{0}` carries the transported
group structure. -/
theorem exists_type0_model (G : Type u) [Group G] [Countable G] :
    ∃ (G₀ : Type) (_ : Group G₀), Nonempty (G ≃* G₀) := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat G
  haveI : Small.{0} G := small_of_injective hf
  exact ⟨Shrink.{0} G, inferInstance, ⟨Shrink.mulEquiv.symm⟩⟩

/-- The `Type 0` model of a countable group is itself countable, so a theorem
whose `Type 0` form carries a countability hypothesis still applies to it. -/
theorem countable_type0_model (G : Type u) [Group G] [Countable G]
    {G₀ : Type} [Group G₀] (e : G ≃* G₀) : Countable G₀ :=
  e.symm.injective.countable

/-- **The pattern, written out once.**  A statement of the form "no countable
group in `Type 0` with such-and-such structure is MF" extends to every universe:
take the `Type 0` model, apply the hypothesis there, and transfer back along the
isomorphism.

The hypothesis is stated as a property of the model rather than as a general
predicate because a predicate quantified over universes is not a Lean object;
each row of the ledger instantiates this shape with its own theorem. -/
theorem not_isOperatorMF_of_type0_model (G : Type u) [Group G] [Countable G]
    (h : ∀ (G₀ : Type) [Group G₀], Nonempty (G ≃* G₀) → ¬ IsOperatorMF G₀) :
    ¬ IsOperatorMF G := by
  obtain ⟨G₀, _, ⟨e⟩⟩ := exists_type0_model G
  exact fun hMF => h G₀ ⟨e⟩ (isOperatorMF_of_mulEquiv e hMF)

/-- The same for residual finiteness, to show the shape is not special to MF. -/
theorem isResiduallyFinite_of_type0_model (G : Type u) [Group G] [Countable G]
    (h : ∀ (G₀ : Type) [Group G₀], Nonempty (G ≃* G₀) → IsResiduallyFinite G₀) :
    IsResiduallyFinite G := by
  obtain ⟨G₀, _, ⟨e⟩⟩ := exists_type0_model G
  exact isResiduallyFinite_of_mulEquiv e.symm (h G₀ ⟨e⟩)

end Type0Transfer
end GroupApproximation
