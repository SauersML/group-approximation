import GroupApproximation.CharClass.LemmaTwoUnitary
import GroupApproximation.CharClass.LemmaTwoBridge

/-!
# Step A as a theorem: an equivalence of the complements yields the corner unitary

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step A).

`CharClass/LemmaTwoUnitary.lean` turns `cs-clutching`'s corner unitary into the
`IsCornerUnitary` field the mapping torus consumes, but it still *takes* the
Murray--von Neumann implementer in the shape
`Analysis/LIXObstructionComplementUnitary.lean` states it, with `colAt` columns.  This
file closes the last gap: an arbitrary continuous equivalence of the two complements
`F ⊕ H` and `𝟏² ⊕ H` produces that data, so `HasStepAUnitary` becomes a **theorem** and
Lemma 2 no longer carries `stepA` as a hypothesis.

Three small facts do the work, all linear algebra with no topology:

* the rank-one projection cut out by a `colAt` column is `rankOneProj`
  (`colAt_mul_conjTranspose_eq_rankOneProj`), so the two vocabularies for `e eᴴ` agree;
* the implementer's **adjoint** has the source and range the corner-unitary theorem wants,
  since that theorem starts from the `e`-complement while `ContinuousMvNEquiv` as stated
  starts from the `s`-complement;
* a partial isometry absorbs its source projection (`mul_source_of_isStarProjection`),
  which is the `w wᴴ w = w` hypothesis.

## Main results

* `isStarProjection_FHmat`, `isStarProjection_EHmat` — the complements are projections.
* `hasStepAUnitary_of_continuousMvNEquiv` — **Step A**.
* `lemmaTwo_of_stepC_stepD` and `lemmaTwo_matrix_of_stepC_stepD` — **Lemma 2 with `stepA`
  discharged**, in the continuous-field and the `C(M, ℂ)`-matrix vocabularies.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. Rank-one projections, in two vocabularies -/

section RankOne

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The rank-one projection cut out by a `colAt` column is `rankOneProj`. -/
theorem colAt_mul_conjTranspose_eq_rankOneProj (k0 : K) (v : K → ℂ) :
    colAt k0 v * (colAt k0 v)ᴴ = rankOneProj v := by
  ext i j
  rw [colAt_mul_colAt_conjTranspose_apply, rankOneProj_apply]

/-- A projection absorbs a rank-one projection built from one of its unit sections, on the
left. -/
theorem mul_rankOneProj_of_mulVec_eq {V : Matrix K K ℂ} {v : K → ℂ} (h : V *ᵥ v = v) :
    V * rankOneProj v = rankOneProj v := by
  ext i j
  rw [Matrix.mul_apply, rankOneProj_apply]
  have hsum : (∑ k, V i k * rankOneProj v k j) = (V *ᵥ v) i * star (v j) := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [rankOneProj_apply, mul_assoc]
  rw [hsum, h]

/-- The same on the right, for a self-adjoint `V`. -/
theorem rankOneProj_mul_of_mulVec_eq {V : Matrix K K ℂ} {v : K → ℂ} (hV : Vᴴ = V)
    (h : V *ᵥ v = v) (k0 : K) : rankOneProj v * V = rankOneProj v := by
  have hc := colAt_mul_colAt_conjTranspose_mul_of_selfAdjoint_of_mulVec_eq hV h k0
  rwa [colAt_mul_conjTranspose_eq_rankOneProj] at hc

/-- **The complement of a unit section is a projection.** -/
theorem isStarProjection_sub_rankOneProj {V : Matrix K K ℂ} (hV : IsStarProjection V)
    {v : K → ℂ} (hv : v ∈ unitVectors K) (h : V *ᵥ v = v) (k0 : K) :
    IsStarProjection (V - rankOneProj v) := by
  have hVs : Vᴴ = V := proj_conjTranspose hV
  have hP : IsStarProjection (rankOneProj v) := isStarProjection_rankOneProj hv
  have hPs : (rankOneProj v)ᴴ = rankOneProj v := proj_conjTranspose hP
  have hl : V * rankOneProj v = rankOneProj v := mul_rankOneProj_of_mulVec_eq h
  have hr : rankOneProj v * V = rankOneProj v := rankOneProj_mul_of_mulVec_eq hVs h k0
  constructor
  · show (V - rankOneProj v) * (V - rankOneProj v) = V - rankOneProj v
    rw [sub_mul, mul_sub, mul_sub, hV.isIdempotentElem.eq, hP.isIdempotentElem.eq, hl, hr]
    abel
  · show star (V - rankOneProj v) = V - rankOneProj v
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sub, hVs, hPs]

open scoped ComplexOrder in
/-- **A partial isometry absorbs its source projection.**  If `Wᴴ W` is a projection then
`W (Wᴴ W) = W`, hence `W Wᴴ W = W`.  `Matrix.conjTranspose_mul_self_eq_zero` needs the
order on `ℂ`, which is scoped. -/
theorem mul_source_of_isStarProjection {W : Matrix K K ℂ}
    (hq : IsStarProjection (Wᴴ * W)) : W * Wᴴ * W = W := by
  have hqs : (Wᴴ * W)ᴴ = Wᴴ * W := proj_conjTranspose hq
  have hidem : (Wᴴ * W) * (Wᴴ * W) = Wᴴ * W := hq.isIdempotentElem.eq
  have hzero : (W * (Wᴴ * W) - W)ᴴ * (W * (Wᴴ * W) - W) = 0 := by
    have e : (W * (Wᴴ * W) - W)ᴴ * (W * (Wᴴ * W) - W)
        = (Wᴴ * W) * (Wᴴ * W) * (Wᴴ * W) - (Wᴴ * W) * (Wᴴ * W)
          - (Wᴴ * W) * (Wᴴ * W) + Wᴴ * W := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hqs]
      noncomm_ring
    rw [e, hidem, hidem]
    abel
  have h := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  have hW : W * (Wᴴ * W) = W := sub_eq_zero.mp h
  rw [← Matrix.mul_assoc] at hW
  exact hW

end RankOne

/-! ## 2. The two complements of the LIX base -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- The distinguished index of `VIdx`, the one `colAt` puts its column at. -/
def vIdxZero (dd : Fin ℓ → ℕ) : VIdx dd := Sum.inl 0

/-- The manuscript's `e`, as a vector of the ambient `ℂ^{VIdx}`. -/
def eSec (m : baseM dd) : VIdx dd → ℂ := Sum.elim (aVec m) 0

/-- The manuscript's `s`, as a vector of the ambient `ℂ^{VIdx}`. -/
def sSec (m : baseM dd) : VIdx dd → ℂ := Sum.elim (bVec m) 0

theorem sumElim_mem_unitVectors {v : Fin 3 → ℂ} (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    (Sum.elim v (0 : HIdx dd → ℂ)) ∈ unitVectors (VIdx dd) := by
  rw [mem_unitVectors_iff, Fintype.sum_sum_type]
  simpa using hv

theorem eSec_mem (m : baseM dd) : eSec m ∈ unitVectors (VIdx dd) :=
  sumElim_mem_unitVectors (aVec_normSq m)

theorem sSec_mem (m : baseM dd) : sSec m ∈ unitVectors (VIdx dd) :=
  sumElim_mem_unitVectors (bVec_normSq m)

theorem eProj_eq_rankOneProj (m : baseM dd) : eProj m = rankOneProj (eSec m) := by
  ext p q
  rw [rankOneProj_apply, eProj, eSec]
  cases p with
  | inl i => cases q with
    | inl j => simp [aVec, eThree]
    | inr j => simp
  | inr i => cases q with
    | inl j => simp
    | inr j => simp

theorem sProj_eq_rankOneProj (m : baseM dd) : sProj m = rankOneProj (sSec m) := by
  ext p q
  rw [rankOneProj_apply, sProj, sSec]
  cases p with
  | inl i => cases q with
    | inl j => simp
    | inr j => simp
  | inr i => cases q with
    | inl j => simp
    | inr j => simp

theorem Vmat_mulVec_eSec (m : baseM dd) : Vmat m *ᵥ eSec m = eSec m :=
  Vmat_mulVec_left m (aVec m)

theorem Vmat_mulVec_sSec (m : baseM dd) : Vmat m *ᵥ sSec m = sSec m :=
  Vmat_mulVec_left m (bVec m)

theorem isStarProjection_FHmat (m : baseM dd) : IsStarProjection (FHmat m) := by
  rw [FHmat, sProj_eq_rankOneProj]
  exact isStarProjection_sub_rankOneProj (isStarProjection_Vmat m) (sSec_mem m)
    (Vmat_mulVec_sSec m) (vIdxZero dd)

theorem isStarProjection_EHmat (m : baseM dd) : IsStarProjection (EHmat m) := by
  rw [EHmat, eProj_eq_rankOneProj]
  exact isStarProjection_sub_rankOneProj (isStarProjection_Vmat m) (eSec_mem m)
    (Vmat_mulVec_eSec m) (vIdxZero dd)

/-! ## 3. Step A -/

/-- **Step A.**  A continuous Murray--von Neumann equivalence of the two complements
`F ⊕ H` and `𝟏² ⊕ H` produces the corner unitary `G` of `V` with `G e = s` that the
mapping torus consumes.

The implementer is used **adjointed**: `ContinuousMvNEquiv FHmat EHmat` has the
`s`-complement as its source, while `exists_continuous_corner_unitary_apply_eq` starts
from the `e`-complement. -/
theorem hasStepAUnitary_of_continuousMvNEquiv
    (h : ContinuousMvNEquiv (FHmat (dd := dd)) EHmat) : HasStepAUnitary dd := by
  obtain ⟨w, hwc, hw1, hw2⟩ := h
  have hsrc : ∀ m, ((w m)ᴴ)ᴴ * (w m)ᴴ
      = Vmat m - colAt (vIdxZero dd) (eSec m) * (colAt (vIdxZero dd) (eSec m))ᴴ := by
    intro m
    rw [Matrix.conjTranspose_conjTranspose, hw2, colAt_mul_conjTranspose_eq_rankOneProj,
      ← eProj_eq_rankOneProj, EHmat]
  have hrng : ∀ m, (w m)ᴴ * ((w m)ᴴ)ᴴ
      = Vmat m - colAt (vIdxZero dd) (sSec m) * (colAt (vIdxZero dd) (sSec m))ᴴ := by
    intro m
    rw [Matrix.conjTranspose_conjTranspose, hw1, colAt_mul_conjTranspose_eq_rankOneProj,
      ← sProj_eq_rankOneProj, FHmat]
  have hpi : ∀ m, (w m)ᴴ * ((w m)ᴴ)ᴴ * (w m)ᴴ = (w m)ᴴ := by
    intro m
    have hq : IsStarProjection ((w m)ᴴ * w m) := by
      rw [hw1]; exact isStarProjection_FHmat m
    have hW : w m * (w m)ᴴ * w m = w m := mul_source_of_isStarProjection hq
    have := congrArg Matrix.conjTranspose hW
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] at this
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    exact this
  exact exists_isCornerUnitary_of_stepA (vIdxZero dd) continuous_Vmat isStarProjection_Vmat
    Vmat_mulVec_eSec Vmat_mulVec_sSec
    (continuous_sumElim_left' continuous_aVec) (continuous_sumElim_left' continuous_bVec)
    (fun m => sum_star_mul_self (eSec_mem m)) (fun m => sum_star_mul_self (sSec_mem m))
    (fun m => (w m)ᴴ) hwc.matrix_conjTranspose hsrc hrng hpi

/-! ## 4. Lemma 2, with Step A discharged -/

/-- **Lemma 2**, in the continuous-field model, with `stepA` gone: only the two
cohomological steps remain as hypotheses. -/
theorem lemmaTwo_of_stepC_stepD {K : Type*} [Zero K]
    (topClass : (↥sphereOne × baseM dd →
      Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) → K)
    (stepC : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      topClass (mappingTorus Vmat G circHoriz circHeight) ≠ 0)
    (stepD : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      topClass (mappingTorus Vmat G circHoriz circHeight) = 0) :
    ¬ ContinuousMvNEquiv (FHmat (dd := dd)) EHmat :=
  not_continuousMvNEquiv topClass hasStepAUnitary_of_continuousMvNEquiv stepC stepD

/-- **Lemma 2**, in the C*-side matrix vocabulary, with `stepA` gone. -/
theorem lemmaTwo_matrix_of_stepC_stepD {K : Type*} [Zero K]
    (topClass : (↥sphereOne × baseM dd →
      Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) → K)
    (stepC : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      topClass (mappingTorus Vmat G circHoriz circHeight) ≠ 0)
    (stepD : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      topClass (mappingTorus Vmat G circHoriz circHeight) = 0) :
    ¬ MurrayVonNeumannEquiv (toMatC (FHmat (dd := dd)) continuous_FHmat)
      (toMatC (EHmat (dd := dd)) continuous_EHmat) :=
  not_murrayVonNeumannEquiv topClass hasStepAUnitary_of_continuousMvNEquiv stepC stepD

end GroupApproximation.CharClass
