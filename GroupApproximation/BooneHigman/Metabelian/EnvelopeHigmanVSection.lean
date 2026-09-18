import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVAlphabet
import GroupApproximation.BooneHigman.RNPresentation.SectionCriterion
import Mathlib.GroupTheory.FreeGroup.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Higman's theorem from a normal-form section over `Fin d`

This module reduces `HigmanVFPStatement` to `HigmanVFinSectionStatement`.  The reduced
statement is the combinatorial core of Higman's theorem for `V_{d,1}`.  It asks for
* finitely many generators `g : Fin n → V_d`,
* finitely many relators `R` in the kernel of `FreeGroup.lift g`,
* a unital section `s : V_d → FreeGroup (Fin n) ⧸ ⟨⟨R⟩⟩` with `s v * of i = s (v * g i)`.

In the intended proof, `s v` is the word read off the reduced tree-pair diagram of `v`.  The
relators say that right multiplication by a generator changes the normal form by a bounded
local move.

Route.
* `higmanVFinFP_of_section`: `FreeGroup.lift g` is surjective because its range is the closure
  of `range g`.  The letters generate the free group (`FreeGroup.closure_range_of`), and the
  free group on `Fin n` is finitely presented.
  `RNPresentation.isFinitelyPresented_of_section` then gives the finite presentation.
* `higmanVFP_of_finSection`: compose with the alphabet transport `higmanVFP_of_fin`.

*Truth.*  Let `V_d` be finitely presented, with `φ : FreeGroup (Fin n) →* V_d` surjective and
`ker φ = ⟨⟨R⟩⟩` for a finite `R`.  Put `g i = φ (of i)`, so that `FreeGroup.lift g = φ`.  Then
`range g` generates `V_d`, and the inverse `s` of `FreeGroup (Fin n) ⧸ ⟨⟨R⟩⟩ ≃* V_d` is a unital
homomorphism.  It satisfies `s (v * g i) = s v * s (φ (of i)) = s v * of i`.  So the statement is
true by Higman's theorem.

*Why it is strictly smaller in proof content.*  The reduction discharges
* the alphabet transport,
* surjectivity of `FreeGroup.lift g` from generation,
* finite presentability of the free group,
* the kernel-through-a-section argument.

What remains is a finite generating set of `V_d` and the normal-form combinatorics of tree-pair
diagrams modulo finitely many relators.  The corpus has neither: no generation lemma for
`higmanThompsonV` and no finite presentation of any `V_{d,1}`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Normal-form section for Higman's theorem over `Fin d`.**  For every `d ≥ 2`, some finite
family of elements generates `higmanThompsonV (Fin d)`.  Finitely many relators lie in the kernel
of the induced map from the free group, and their quotient carries a unital section that
intertwines right multiplication by the letters with right multiplication by the generators. -/
def HigmanVFinSectionStatement : Prop :=
  ∀ d : ℕ, 1 < d →
    ∃ (n : ℕ) (g : Fin n → ↥(higmanThompsonV (Fin d))), Subgroup.closure (Set.range g) = ⊤ ∧
      ∃ R : Set (FreeGroup (Fin n)), R.Finite ∧ R ⊆ (FreeGroup.lift g).ker ∧
        ∃ s : ↥(higmanThompsonV (Fin d)) → FreeGroup (Fin n) ⧸ Subgroup.normalClosure R,
          s 1 = 1 ∧
            ∀ (v : ↥(higmanThompsonV (Fin d))) (i : Fin n),
              s v * ((FreeGroup.of i : FreeGroup (Fin n)) :
                FreeGroup (Fin n) ⧸ Subgroup.normalClosure R) = s (v * g i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVFinSectionStatement

/-- The normal-form section gives Higman's theorem over `Fin d`. -/
theorem higmanVFinFP_of_section (h : HigmanVFinSectionStatement) : HigmanVFinFPStatement := by
  intro d hd
  obtain ⟨n, g, hg, R, hR, hRker, s, hs1, hmul⟩ := h d hd
  refine RNPresentation.isFinitelyPresented_of_section (FreeGroup.lift g) ?_ R hR hRker
    (Set.range FreeGroup.of) (FreeGroup.closure_range_of (Fin n)) s hs1 ?_
  · rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]
    exact hg
  · rintro v _ ⟨i, rfl⟩
    rw [FreeGroup.lift_apply_of]
    exact hmul v i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFinFP_of_section

/-- **Higman's theorem from the normal-form section.**  The section statement over the
alphabets `Fin d` gives `HigmanVFPStatement`. -/
theorem higmanVFP_of_finSection (h : HigmanVFinSectionStatement) : HigmanVFPStatement :=
  higmanVFP_of_fin (higmanVFinFP_of_section h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_of_finSection

/-- The normal-form section for `V_d` and the core normal form for `V_X(H)` give the full
normal-form section statement. -/
theorem rnFreeSection_of_finSection_core (hV : HigmanVFinSectionStatement)
    (hcore : RNFreeSectionCoreStatement) : RNFreeSectionStatement :=
  rnFreeSection_of_higmanV_core (higmanVFP_of_finSection hV) hcore

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnFreeSection_of_finSection_core

end GroupApproximation.BooneHigman.Metabelian.Envelope
