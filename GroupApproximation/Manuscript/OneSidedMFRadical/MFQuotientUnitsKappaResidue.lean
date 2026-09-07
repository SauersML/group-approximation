import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKOne

/-!
# Half of Ara--Goodearl--Pardo Theorem 2.4 is now free

`MFQuotientUnitsKOne.lean` quotes AGP Theorem 2.4 as `AGPUnitKappa`: for a
countable purely infinite simple ring, the canonical `κ : Rˣ → K₁(R)` is
surjective **and** has kernel exactly the commutator subgroup.

One of the two clauses of "kernel exactly the commutator subgroup" no longer
needs the citation.  `KOne/AlgebraicKOne.lean` proves `K₁(R)` **abelian**
(`AlgebraicK.algebraicKOneCommGroup`, from Whitehead's lemma), and a
homomorphism into an abelian group kills commutators.  So

  `commutator Rˣ ≤ (kappa R).ker`

is a theorem, for **every** ring, with no hypothesis on `R` at all — not
countability, not simplicity, not pure infiniteness.

## What is left of Theorem 2.4

`AGPUnitKappaResidue` is the citation with that half removed: surjectivity of
`κ`, and the reverse containment `ker κ ≤ commutator Rˣ`.  Those two are the
substance, and they are what AGP's Steps 1 and 2 — the manuscript's clauses (a)
and (b), quoted in `MFQuotientUnits.lean` as `AGPStepOne` and
`AGPMenalMoncasiReduction` — actually establish.  `agpUnitKappa_of_residue`
rebuilds the full citation from the residue, so every existing consumer is
unaffected.

This is not a weakening of what the paper asks a reader to grant; it is the same
grant with one clause moved from "cited" to "proved".
-/

namespace GroupApproximation
namespace MFQuotientUnitsKOne

open MFQuotientUnits
open AlgebraicK

/-- **`κ` kills commutators**, because `K₁(R)` is abelian.

No hypothesis on `R`: this is Whitehead's lemma talking, not pure
infiniteness. -/
theorem commutator_le_kappa_ker (R : Type) [Ring R] :
    commutator Rˣ ≤ (kappa R).ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

/-- **Ara--Goodearl--Pardo, Theorem 2.4, with the free half removed.**

Surjectivity of `κ`, and the containment that is genuinely AGP's — the reverse
one.  The containment `commutator Rˣ ≤ ker κ` is not here because
`commutator_le_kappa_ker` proves it. -/
def AGPUnitKappaResidue : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    Function.Surjective (kappa R) ∧ (kappa R).ker ≤ commutator Rˣ

/-- The residue rebuilds the full citation, so no consumer of `AGPUnitKappa`
changes. -/
theorem agpUnitKappa_of_residue (h : AGPUnitKappaResidue) : AGPUnitKappa := by
  intro R _ _ hR
  obtain ⟨hsurj, hle⟩ := h R hR
  exact ⟨hsurj, le_antisymm hle (commutator_le_kappa_ker R)⟩

end MFQuotientUnitsKOne
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnitsKOne.commutator_le_kappa_ker
#audit_axioms GroupApproximation.MFQuotientUnitsKOne.agpUnitKappa_of_residue
