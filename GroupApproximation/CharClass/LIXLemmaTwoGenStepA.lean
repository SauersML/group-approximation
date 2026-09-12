import GroupApproximation.CharClass.LemmaTwoStepA
import GroupApproximation.Analysis.LIXLemmaTwoPropGeneric
import GroupApproximation.Meta.AxiomGuard

/-!
# Step A at rank `n`, for an arbitrary unit section

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.6; lead's ruling of 2026-09-11 assigning the
rank-`n` Step A and the glue of Lemma 2 to this lane).

`CharClass/LemmaTwoStepA.lean` proves, at rank two and for the tautological section, that a
continuous Murray--von Neumann equivalence of the two complements produces the corner
unitary the mapping torus consumes (`hasStepAUnitary_of_continuousMvNEquiv`).  This file
ports that argument to the rank-`n` shape layer of `CharClass/LIXShapeGeneric.lean`, and to
an **arbitrary** continuous unit section `b` of the trivial block, because the endpoint's
seam `LIX.Gen.LemmaTwoFor n dd b` (`Analysis/LIXLemmaTwoPropGeneric.lean`) is stated for an
arbitrary section and the powers programme instantiates it at the degree-`k` sections.

Nothing is re-derived.  The corner-unitary construction is `cs-clutching`'s, reached through
`exists_isCornerUnitary_of_stepA`, and the three linear-algebra facts are the rank-free ones
of `LemmaTwoStepA.lean` (`colAt_mul_conjTranspose_eq_rankOneProj`,
`isStarProjection_sub_rankOneProj`, `mul_source_of_isStarProjection`).  The only rank-`n`
input is that `fromBlocks (x xᴴ) 0 0 0` is the rank-one projection of `(x, 0)`.

## Main results

* `Gen.fromBlocks_rankOneProj_zero` — the rank-one projection of a trivial-block vector.
* `Gen.isStarProjection_FHmatOf`, `Gen.isStarProjection_EHmat` — both complements are
  projections, at every rank and for every unit section.
* `Gen.exists_cornerUnitary_of_continuousMvNEquiv` — **Step A at rank `n`**: an equivalence
  of `FHmatOf n b` with `EHmat n` gives a continuous corner unitary `G` with
  `G (e_last, 0) = (b, 0)`.
* `Gen.hasStepAUnitary_of_continuousMvNEquiv` — the producer of `Gen.HasStepAUnitary n dd`.
* `hasStepAUnitary_of_continuousMvNEquiv_of_gen` — the landed rank-two Step A, re-derived at
  `n = 2` through `sp-tower`'s `rfl` bridges.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

namespace Gen

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. Rank-one projections of trivial-block vectors -/

/-- A vector of the trivial block, extended by zero on `H`, is a unit vector of the ambient
as soon as it is one of `ℂ^{n+1}`. -/
theorem sumElimZero_mem_unitVectors (n : ℕ) {v : Fin (n + 1) → ℂ}
    (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    (Sum.elim v (0 : HIdx dd → ℂ)) ∈ unitVectors (VIdx n dd) := by
  rw [mem_unitVectors_iff, Fintype.sum_sum_type]
  simpa using hv

/-- The rank-one projection of `u` in the trivial block is the rank-one projection of
`(u, 0)` in the ambient. -/
theorem fromBlocks_rankOneProj_zero (n : ℕ) (u : Fin (n + 1) → ℂ) :
    (Matrix.fromBlocks (rankOneProj u) 0 0 0 : Matrix (VIdx n dd) (VIdx n dd) ℂ)
      = rankOneProj (Sum.elim u (0 : HIdx dd → ℂ)) := by
  ext p q
  rw [rankOneProj_apply]
  cases p with
  | inl i => cases q with
    | inl j => simp
    | inr j => simp
  | inr i => cases q with
    | inl j => simp
    | inr j => simp

/-! ## 2. The two complements are projections -/

/-- **The complement of an arbitrary unit section is a projection**, at every rank. -/
theorem isStarProjection_FHmatOf (n : ℕ) {b : baseM n dd → Fin (n + 1) → ℂ}
    (hb : ∀ m, ∑ i, ‖b m i‖ ^ 2 = 1) (m : baseM n dd) :
    IsStarProjection (LIX.Gen.FHmatOf n b m) := by
  rw [LIX.Gen.FHmatOf, fromBlocks_rankOneProj_zero]
  exact isStarProjection_sub_rankOneProj (isStarProjection_Vmat n m)
    (sumElimZero_mem_unitVectors n (hb m)) (Vmat_mulVec_left n m (b m)) (Sum.inl 0)

/-- **The complement of the constant section is a projection**, at every rank. -/
theorem isStarProjection_EHmat (n : ℕ) (m : baseM n dd) : IsStarProjection (EHmat n m) := by
  rw [EHmat, eProj, fromBlocks_rankOneProj_zero]
  exact isStarProjection_sub_rankOneProj (isStarProjection_Vmat n m)
    (sumElimZero_mem_unitVectors n (eLast_normSq n)) (Vmat_mulVec_left n m (eLast n))
    (Sum.inl 0)

/-! ## 3. Step A at rank `n` -/

/-- **Step A at rank `n`, for an arbitrary unit section.**  A continuous Murray--von Neumann
equivalence of the complement of `b` with the complement of the constant section `e_last`
produces a continuous corner unitary `G` of `V` carrying `(e_last, 0)` to `(b, 0)`.

The implementer is used **adjointed**, as at rank two: `ContinuousMvNEquiv (FHmatOf n b)
(EHmat n)` has the `b`-complement as its source, while `exists_isCornerUnitary_of_stepA`
starts from the `e`-complement. -/
theorem exists_cornerUnitary_of_continuousMvNEquiv (n : ℕ) {b : baseM n dd → Fin (n + 1) → ℂ}
    (hbc : Continuous b) (hb : ∀ m, ∑ i, ‖b m i‖ ^ 2 = 1)
    (h : ContinuousMvNEquiv (LIX.Gen.FHmatOf n b) (EHmat n)) :
    ∃ G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ, Continuous G ∧
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) ∧
      (∀ m, G m *ᵥ Sum.elim (eLast n) (0 : HIdx dd → ℂ) = Sum.elim (b m) 0) := by
  obtain ⟨w, hwc, hw1, hw2⟩ := h
  have hsrc : ∀ m, ((w m)ᴴ)ᴴ * (w m)ᴴ
      = Vmat n m - colAt (Sum.inl 0 : VIdx n dd) (Sum.elim (eLast n) 0)
          * (colAt (Sum.inl 0 : VIdx n dd) (Sum.elim (eLast n) 0))ᴴ := by
    intro m
    rw [Matrix.conjTranspose_conjTranspose, hw2, colAt_mul_conjTranspose_eq_rankOneProj,
      EHmat, eProj, fromBlocks_rankOneProj_zero]
  have hrng : ∀ m, (w m)ᴴ * ((w m)ᴴ)ᴴ
      = Vmat n m - colAt (Sum.inl 0 : VIdx n dd) (Sum.elim (b m) 0)
          * (colAt (Sum.inl 0 : VIdx n dd) (Sum.elim (b m) 0))ᴴ := by
    intro m
    rw [Matrix.conjTranspose_conjTranspose, hw1, colAt_mul_conjTranspose_eq_rankOneProj,
      LIX.Gen.FHmatOf, fromBlocks_rankOneProj_zero]
  have hpi : ∀ m, (w m)ᴴ * ((w m)ᴴ)ᴴ * (w m)ᴴ = (w m)ᴴ := by
    intro m
    have hq : IsStarProjection ((w m)ᴴ * w m) := by
      rw [hw1]; exact isStarProjection_FHmatOf n hb m
    have hW : w m * (w m)ᴴ * w m = w m := mul_source_of_isStarProjection hq
    have := congrArg Matrix.conjTranspose hW
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] at this
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    exact this
  exact exists_isCornerUnitary_of_stepA (Sum.inl 0 : VIdx n dd)
    (e := fun _ => Sum.elim (eLast n) 0) (s := fun m => Sum.elim (b m) 0)
    (continuous_Vmat n) (isStarProjection_Vmat n)
    (fun m => Vmat_mulVec_left n m (eLast n)) (fun m => Vmat_mulVec_left n m (b m))
    (continuous_sumElim_left' continuous_const) (continuous_sumElim_left' hbc)
    (fun _ => sum_star_mul_self (sumElimZero_mem_unitVectors n (eLast_normSq n)))
    (fun m => sum_star_mul_self (sumElimZero_mem_unitVectors n (hb m)))
    (fun m => (w m)ᴴ) hwc.matrix_conjTranspose hsrc hrng hpi

/-- **The producer of `Gen.HasStepAUnitary n dd`**: Step A at the tautological section. -/
theorem hasStepAUnitary_of_continuousMvNEquiv (n : ℕ)
    (h : ContinuousMvNEquiv (FHmat (dd := dd) n) (EHmat n)) : HasStepAUnitary n dd :=
  exists_cornerUnitary_of_continuousMvNEquiv n (continuous_bVec n) (bVec_normSq n) h

end Gen

/-! ## 4. The rank-two bridge

The landed rank-two Step A, statement for statement, proved by the generic one at `n = 2`.
It exercises `sp-tower`'s `rfl` bridges (`FHmat ≡ Gen.FHmat 2`, `EHmat ≡ Gen.EHmat 2`,
`HasStepAUnitary dd ≡ Gen.HasStepAUnitary 2 dd`) inside the hypothesis of a theorem. -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

theorem hasStepAUnitary_of_continuousMvNEquiv_of_gen
    (h : ContinuousMvNEquiv (FHmat (dd := dd)) EHmat) : HasStepAUnitary dd :=
  Gen.hasStepAUnitary_of_continuousMvNEquiv 2 h

#audit_axioms Gen.sumElimZero_mem_unitVectors
#audit_axioms Gen.fromBlocks_rankOneProj_zero
#audit_axioms Gen.isStarProjection_FHmatOf
#audit_axioms Gen.isStarProjection_EHmat
#audit_axioms Gen.exists_cornerUnitary_of_continuousMvNEquiv
#audit_axioms Gen.hasStepAUnitary_of_continuousMvNEquiv
#audit_axioms hasStepAUnitary_of_continuousMvNEquiv_of_gen

end GroupApproximation.CharClass

end
