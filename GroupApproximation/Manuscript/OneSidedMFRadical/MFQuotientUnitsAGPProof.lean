import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKappaProof

/-!
# Every Ara--Goodearl--Pardo proposition of `thm:mf-quotient-units`, discharged

`non_mf_groups_exist.tex`, the proof of Theorem `thm:mf-quotient-units`
(tex lines 1178--1223), names Ara--Goodearl--Pardo four times:

> The ring `M_n(R)` is again countable, purely infinite, and simple
> \[AGP, Corollary~1.7\] …  Ara, Goodearl, and Pardo show that `κ` is surjective
> with kernel `[H,H]` \[AGP, Theorem~2.4\] …  Every nonzero idempotent `e` of
> `R` is infinite \[AGP, Proposition~1.5\] …  We use two facts from the proof
> of \[AGP, Theorem~2.4\] …

Each of those is a named proposition somewhere in this development, and each is
now a theorem rather than a hypothesis.  This module collects them.

## What was already proved elsewhere, and what is new here

Already proved: `MFQuotientUnitsMatrixReduction.agpMatrixReduction` (Corollary
1.7), `MFQuotientUnitsKappaProof.agpUnitKappa` (Theorem 2.4 for the canonical
`κ : Rˣ → K₁(R)` of `KOne/AlgebraicKOne.lean`),
`MFQuotientUnitsReductionProof.agpMenalMoncasiReduction` (the printed step (a),
the Menal--Moncasi matrix reduction) and
`MFQuotientUnitsStepOne.agpStepOne` (the printed step (b), the corner
isomorphism `θ`).

New here: `agpUnitKappaResidue`, the one proposition of the family that was
stated but never discharged.  `MFQuotientUnitsKappaResidue.lean` introduced
`AGPUnitKappaResidue` — Theorem 2.4 with the clause that Whitehead's lemma makes
free (`commutator Rˣ ≤ ker κ`) removed — and proved only that the residue
rebuilds the full citation, leaving the residue itself as an assumption.  Since
`agpUnitKappa` now proves the full citation, the residue follows from it, and
the citation is gone from both directions.

`manuscriptAGPInputs` is the single closed statement that says so: the
conjunction of all six named Ara--Goodearl--Pardo propositions of this proof,
with no binder in front of it.
-/

namespace GroupApproximation
namespace MFQuotientUnitsKOne

open MFQuotientUnits AlgebraicK

/-! ### The residue -/

/-- **Ara--Goodearl--Pardo, Theorem 2.4, with the free clause removed** — proved.

The printed sentence is

> Ara, Goodearl, and Pardo show that `κ` is surjective with kernel `[H,H]`
> \[AGP, Theorem~2.4\]

(tex line 1182).  `commutator_le_kappa_ker` proves one half of "kernel `[H,H]`"
for every ring, from Whitehead's lemma alone; `AGPUnitKappaResidue` is what is
left, namely surjectivity of `κ` together with `ker κ ≤ commutator Rˣ`.  Both
come from `agpUnitKappa`, which proves the citation outright. -/
theorem agpUnitKappaResidue : AGPUnitKappaResidue := by
  intro R _ _ hR
  obtain ⟨hsurj, hker⟩ := agpUnitKappa R hR
  exact ⟨hsurj, hker.le⟩

/-- The round trip through `MFQuotientUnitsKappaResidue.lean` closes: the
residue, plus the clause Whitehead's lemma supplies, is the citation again. -/
theorem agpUnitKappa_of_agpUnitKappaResidue : AGPUnitKappa :=
  agpUnitKappa_of_residue agpUnitKappaResidue

/-! ### The whole family, in one closed proposition -/

/-- **Every Ara--Goodearl--Pardo proposition quoted by the printed proof of
`thm:mf-quotient-units`.**

In printed order: Corollary 1.7 (`AGPMatrixReduction`), Theorem 2.4 for the
canonical `κ` (`AGPUnitKappa`) and its residue (`AGPUnitKappaResidue`), Theorem
2.4 with the target supplied abstractly (`AGPUnitK1`), and the two facts taken
from the proof of Theorem 2.4 — step (a), the Menal--Moncasi reduction
(`AGPMenalMoncasiReduction`), and step (b), the corner isomorphism
(`AGPStepOne`).

Proposition 1.5 of the same paper is not listed separately: the printed proof
uses it only through the corner-unit display `eq:corner-units`, and its
consumers reach it through `MFQuotientUnitsStepOne.isInfiniteIdempotent_of_ne_zero`,
which is a theorem about `IsPurelyInfiniteSimpleRing` and not a named
citation. -/
def PrintedAGPInputs : Prop :=
  AGPMatrixReduction ∧ AGPUnitKappa ∧ AGPUnitKappaResidue ∧ AGPUnitK1 ∧
    AGPMenalMoncasiReduction ∧ AGPStepOne

/-- **The printed proof of `thm:mf-quotient-units` quotes Ara--Goodearl--Pardo
for nothing that is not proved here.** -/
theorem manuscriptAGPInputs : PrintedAGPInputs :=
  ⟨agpMatrixReduction, agpUnitKappa, agpUnitKappaResidue,
    agpUnitK1_of_kappa agpUnitKappa, agpMenalMoncasiReduction, agpStepOne⟩

end MFQuotientUnitsKOne
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.agpUnitKappaResidue
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.agpUnitKappa_of_agpUnitKappaResidue
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptAGPInputs
