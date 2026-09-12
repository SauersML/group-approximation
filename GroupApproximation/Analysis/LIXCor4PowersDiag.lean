import GroupApproximation.Analysis.LIXCor4PowersDiagChain
import GroupApproximation.Analysis.LIXCor4PowersAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# `diag(ũ ⊕ 1, 1)` is null-homotopic in `M₂(A₀)`, at every rank, and the arrow `Corollary4Powers`

This file discharges `Gen.DiagWitnessNullHomotopic n hn`, the one input
`Analysis/LIXCor4PowersAssembly.lean` names, and so proves
`NinetyNineProblems.Corollary4Powers n (degreeFamily n)` for every `n ≥ 1`.

By `Analysis/LIXCor4PowersDiagChain.lean` it suffices to contract the block section
`ũ ⊕ 1` over `𝟏^n ⊕ 𝟏^n` in the section algebra over `X₀ = S^{2n}`, where paths are pointwise.
`ũ = Aᴴ u`, and the section splits as `(Aᴴ ⊕ 1)·(u ⊕ 1)`.

* **`u ⊕ 1` contracts** (`sectionBlock_genU2_mem`).  For any continuous equatorial unit field
  `ξ`, `genU2 ξ ⊕ 1_n` is `genU ξ ⊕ 1_{n-1}` read in the rearrangement
  `𝟏^n ⊕ 𝟏^n = 𝟏^{n+1} ⊕ 𝟏^{n-1}` that sends the pole to the first vector of the second block
  (`blockEquiv`), and `genU ξ` contracts through `seamPath`, pointwise.  This is `hdiag` of the
  rank-two chain, with no appeal to `π_{2n}(U(2n)) = 0`: the rotation happens inside `U(n+1)`.
* **`Aᴴ ⊕ 1` contracts** (`sectionBlock_wallA_mem`).  `A` is a ball unitary, so `t ↦ A(t·v)ᴴ ⊕ 1`
  runs from `Aᴴ ⊕ 1` to the constant `A(0)ᴴ ⊕ 1`, and `A(0) = genU2 (equatorEmb ε₀)`
  (`Powers.ballWall_genSphere_zero`), whose block section contracts by the first bullet at a
  constant field.  No path-connectedness of `U(n)` anywhere.

## Main results

* `Gen.diagWitnessNullHomotopic` — **`diag(ũ ⊕ 1, 1) ∈ U₀(M₂(A₀))` at every rank `n ≥ 1`**.
* `Gen.corollary4Powers` — **`Corollary4Powers n (degreeFamily n)`**, with no hypothesis.
-/

namespace GroupApproximation
namespace LIX
namespace Gen

open scoped Matrix ComplexOrder CStarAlgebra

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Paths in the section algebra -/

section Paths

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A jointly continuous family of matrix fields, as a path in the section algebra. -/
def secPath (F : unitInterval → X → Matrix ι ι ℂ)
    (hF : Continuous fun q : unitInterval × X => F q.1 q.2) :
    C(unitInterval, STW59.SectionAlgebra X ι) :=
  (⟨fun q : unitInterval × X => F q.1 q.2, hF⟩ : C(unitInterval × X, Matrix ι ι ℂ)).curry

/-- The path as a family of unitaries. -/
def secPathU (F : unitInterval → X → Matrix ι ι ℂ)
    (hF : Continuous fun q : unitInterval × X => F q.1 q.2)
    (hu₁ : ∀ t w, (F t w)ᴴ * F t w = 1) (hu₂ : ∀ t w, F t w * (F t w)ᴴ = 1) (t : unitInterval) :
    unitary (STW59.SectionAlgebra X ι) :=
  ⟨secPath F hF t, ContinuousMap.ext fun w => hu₁ t w, ContinuousMap.ext fun w => hu₂ t w⟩

theorem joined_secPathU (F : unitInterval → X → Matrix ι ι ℂ)
    (hF : Continuous fun q : unitInterval × X => F q.1 q.2)
    (hu₁ : ∀ t w, (F t w)ᴴ * F t w = 1) (hu₂ : ∀ t w, F t w * (F t w)ᴴ = 1) :
    Joined (secPathU F hF hu₁ hu₂ 0) (secPathU F hF hu₁ hu₂ 1) :=
  ⟨⟨⟨secPathU F hF hu₁ hu₂, continuous_induced_rng.mpr (secPath F hF).continuous⟩, rfl, rfl⟩⟩

/-- **A path ending at `1` puts its start in `U₀`.** -/
theorem secPathU_zero_mem (F : unitInterval → X → Matrix ι ι ℂ)
    (hF : Continuous fun q : unitInterval × X => F q.1 q.2)
    (hu₁ : ∀ t w, (F t w)ᴴ * F t w = 1) (hu₂ : ∀ t w, F t w * (F t w)ᴴ = 1)
    (h1 : ∀ w, F 1 w = 1) :
    secPathU F hF hu₁ hu₂ 0 ∈ unitaryComponentOne (STW59.SectionAlgebra X ι) := by
  refine mem_unitaryComponentOne_iff.mpr ?_
  have h := joined_secPathU F hF hu₁ hu₂
  have hone : secPathU F hF hu₁ hu₂ 1 = 1 := Subtype.ext (ContinuousMap.ext fun w => h1 w)
  rw [hone] at h
  exact h.symm

/-- **A path starting in `U₀` ends in `U₀`.** -/
theorem secPathU_one_mem (F : unitInterval → X → Matrix ι ι ℂ)
    (hF : Continuous fun q : unitInterval × X => F q.1 q.2)
    (hu₁ : ∀ t w, (F t w)ᴴ * F t w = 1) (hu₂ : ∀ t w, F t w * (F t w)ᴴ = 1)
    (h0 : secPathU F hF hu₁ hu₂ 0 ∈ unitaryComponentOne (STW59.SectionAlgebra X ι)) :
    secPathU F hF hu₁ hu₂ 1 ∈ unitaryComponentOne (STW59.SectionAlgebra X ι) :=
  mem_unitaryComponentOne_iff.mpr
    ((mem_unitaryComponentOne_iff.mp h0).trans (joined_secPathU F hF hu₁ hu₂))

end Paths

/-! ## 2. The generator fixes the pole, entrywise -/

section Entries

variable {n : ℕ}

-- the `simp` calls below close different goals with different subsets of their arguments
set_option linter.unusedSimpArgs false

theorem genU_apply_last_right {x : Fin (n + 1) → ℂ} (hx : x ∈ STW59.unitVectors (Fin (n + 1)))
    (hN : x (Fin.last n) ≠ -1) (hS : x (Fin.last n) ≠ 1) (i : Fin (n + 1)) :
    genU n x i (Fin.last n) = ePole n i := by
  have h := congrFun₂ (genU_mul_rk1 hx hN hS (ePole n)) i (Fin.last n)
  simpa [Matrix.mul_apply, rk1_apply, ePole, Pi.single_apply] using h

theorem genU_apply_last_left {x : Fin (n + 1) → ℂ} (hx : x ∈ STW59.unitVectors (Fin (n + 1)))
    (hN : x (Fin.last n) ≠ -1) (hS : x (Fin.last n) ≠ 1) (j : Fin (n + 1)) :
    genU n x (Fin.last n) j = ePole n j := by
  have h := congrFun₂ (rk1_ePole_mul_genU hx hN hS) (Fin.last n) j
  simpa [Matrix.mul_apply, rk1_apply, ePole, Pi.single_apply] using h

/-- The `n × n` block of the generator, entrywise. -/
theorem genU2_apply_eq (x : Fin (n + 1) → ℂ) (a b : Fin n) :
    genU2 n x a b = genU n x a.castSucc b.castSucc := by
  simp [genU2, Matrix.mul_apply, incl_apply, Matrix.conjTranspose_apply, apply_ite star,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

end Entries

/-! ## 3. The rearrangement `𝟏^{m+1} ⊕ 𝟏^{m+1} ≃ 𝟏^{m+2} ⊕ 𝟏^m` -/

section Rearrange

variable {m : ℕ}

/-- The first block goes to the first `m + 1` coordinates of `ℂ^{m+2}`; the first vector of the
second block goes to the pole; the rest of the second block goes to `ℂ^m`. -/
def blockEquiv (m : ℕ) : Fin (m + 1) ⊕ Fin (m + 1) ≃ Fin (m + 1 + 1) ⊕ Fin m where
  toFun := Sum.elim (fun a => Sum.inl a.castSucc)
    (fun b => Fin.cases (motive := fun _ => Fin (m + 1 + 1) ⊕ Fin m) (Sum.inl (Fin.last (m + 1)))
      (fun d => Sum.inr d) b)
  invFun := Sum.elim
    (fun c => Fin.lastCases (motive := fun _ => Fin (m + 1) ⊕ Fin (m + 1)) (Sum.inr 0)
      (fun a => Sum.inl a) c)
    (fun d => Sum.inr d.succ)
  left_inv := by
    rintro (a | b)
    · simp
    · cases b using Fin.cases with
      | zero => simp
      | succ d => simp
  right_inv := by
    rintro (c | d)
    · cases c using Fin.lastCases with
      | last => simp
      | cast a => simp
    · simp

-- `simp` below closes sixteen branches with different subsets of its arguments
set_option linter.unusedSimpArgs false in
/-- **`genU x ⊕ 1_m`, read in the rearrangement, is `genU2 x ⊕ 1_{m+1}`.** -/
theorem submatrix_genU_blockEquiv {x : Fin (m + 1 + 1) → ℂ} (hx : x ∈ STW59.unitVectors (Fin (m + 1 + 1)))
    (hN : x (Fin.last (m + 1)) ≠ -1) (hS : x (Fin.last (m + 1)) ≠ 1) :
    (Matrix.fromBlocks (genU (m + 1) x) 0 0 (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix
        (blockEquiv m) (blockEquiv m)
      = Matrix.fromBlocks (genU2 (m + 1) x) 0 0 1 := by
  ext r s
  rcases r with a | b <;> rcases s with a' | b'
  · simp [blockEquiv, genU2_apply_eq]
  · cases b' using Fin.cases with
    | zero =>
      simp [blockEquiv, genU_apply_last_right hx hN hS, ePole, Pi.single_apply,
        (Fin.castSucc_lt_last a).ne]
    | succ d => simp [blockEquiv]
  · cases b using Fin.cases with
    | zero =>
      simp [blockEquiv, genU_apply_last_left hx hN hS, ePole, Pi.single_apply,
        (Fin.castSucc_lt_last a').ne]
    | succ d => simp [blockEquiv]
  · cases b using Fin.cases with
    | zero =>
      cases b' using Fin.cases with
      | zero => simp [blockEquiv, genU_apply_last_left hx hN hS, ePole, Matrix.one_apply]
      | succ d' => simp [blockEquiv, Matrix.one_apply, (Fin.succ_ne_zero d').symm]
    | succ d =>
      cases b' using Fin.cases with
      | zero => simp [blockEquiv, Matrix.one_apply, Fin.succ_ne_zero d]
      | succ d' => simp [blockEquiv, Matrix.one_apply, Fin.succ_inj]

end Rearrange

/-! ## 4. `genU2 ξ ⊕ 1` contracts -/

section GenBlock

variable {m : ℕ}

set_option linter.unusedSimpArgs false

/-- The contraction of `genU ξ ⊕ 1_m`, read in the rearrangement. -/
def seamBlockPath (m : ℕ) (ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ)
    (t : unitInterval) (w : STW59.Gen.baseX (m + 1) 0) :
    Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) ℂ :=
  (Matrix.fromBlocks (seamPath (ePole (m + 1)) (t : ℝ) (ξ w.1)) 0 0
    (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix (blockEquiv m) (blockEquiv m)

/-- A continuous field of equatorial unit vectors. -/
structure IsEquatorField (m : ℕ) (ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ) :
    Prop where
  continuous : Continuous ξ
  mem : ∀ v, ξ v ∈ STW59.unitVectors (Fin (m + 1 + 1))
  equator : ∀ v, (ξ v (Fin.last (m + 1))).re = 0

theorem continuous_seamBlockPath {ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ}
    (hξ : IsEquatorField m ξ) :
    Continuous fun q : unitInterval × STW59.Gen.baseX (m + 1) 0 => seamBlockPath m ξ q.1 q.2 := by
  have hs : Continuous fun q : unitInterval × STW59.Gen.baseX (m + 1) 0 =>
      seamPath (ePole (m + 1)) (q.1 : ℝ) (ξ q.2.1) :=
    continuous_seamPath (continuous_subtype_val.comp continuous_fst)
      (hξ.continuous.comp (continuous_fst.comp continuous_snd))
      (fun q => isFrameDatum_contractNorth (unit_ePole (m + 1))
        (isEquator_ePole (hξ.mem q.2.1) (hξ.equator q.2.1)) q.1.2.1 q.1.2.2)
      (fun q => isFrameDatum_contractSouth (unit_ePole (m + 1))
        (isEquator_ePole (hξ.mem q.2.1) (hξ.equator q.2.1)) q.1.2.1 q.1.2.2)
  exact (Continuous.matrix_fromBlocks hs continuous_const continuous_const
    continuous_const).matrix_submatrix _ _

theorem seamBlockPath_star_mul {ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ}
    (hξ : IsEquatorField m ξ) (t : unitInterval) (w : STW59.Gen.baseX (m + 1) 0) :
    (seamBlockPath m ξ t w)ᴴ * seamBlockPath m ξ t w = 1 := by
  have h := (seamPath_ePole_unitary (hξ.mem w.1) (hξ.equator w.1) t.2.1 t.2.2).1
  rw [seamBlockPath, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, h]
  simp

theorem seamBlockPath_mul_star {ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ}
    (hξ : IsEquatorField m ξ) (t : unitInterval) (w : STW59.Gen.baseX (m + 1) 0) :
    seamBlockPath m ξ t w * (seamBlockPath m ξ t w)ᴴ = 1 := by
  have h := (seamPath_ePole_unitary (hξ.mem w.1) (hξ.equator w.1) t.2.1 t.2.2).2
  rw [seamBlockPath, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, h]
  simp

theorem continuous_genU2_field {ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ}
    (hξ : IsEquatorField m ξ) : Continuous fun v => genU2 (m + 1) (ξ v) :=
  continuous_genU2 (m + 1) hξ.continuous hξ.mem
    (fun v => ne_neg_one_of_re_eq_zero (hξ.equator v))
    (fun v => ne_one_of_re_eq_zero (hξ.equator v))

theorem genU2_field_star_mul {ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ}
    (hξ : IsEquatorField m ξ) (v : ↥(STW59.Gen.sphereEven (m + 1))) :
    (genU2 (m + 1) (ξ v))ᴴ * genU2 (m + 1) (ξ v) = 1 :=
  genU2_conjTranspose_mul_self (m + 1) (hξ.mem v) (ne_neg_one_of_re_eq_zero (hξ.equator v))
    (ne_one_of_re_eq_zero (hξ.equator v))

theorem genU2_field_mul_star {ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ}
    (hξ : IsEquatorField m ξ) (v : ↥(STW59.Gen.sphereEven (m + 1))) :
    genU2 (m + 1) (ξ v) * (genU2 (m + 1) (ξ v))ᴴ = 1 :=
  genU2_mul_conjTranspose (m + 1) (hξ.mem v) (ne_neg_one_of_re_eq_zero (hξ.equator v))
    (ne_one_of_re_eq_zero (hξ.equator v))

/-- **`genU2 ξ ⊕ 1` is null-homotopic in the section algebra over `X₀`.** -/
theorem sectionBlock_genU2_mem {ξ : ↥(STW59.Gen.sphereEven (m + 1)) → Fin (m + 1 + 1) → ℂ}
    (hξ : IsEquatorField m ξ) :
    sectionBlock (m + 1) (fun v => genU2 (m + 1) (ξ v)) (continuous_genU2_field hξ)
        (genU2_field_star_mul hξ) (genU2_field_mul_star hξ)
      ∈ unitaryComponentOne
          (STW59.SectionAlgebra (STW59.Gen.baseX (m + 1) 0) (Fin (m + 1) ⊕ Fin (m + 1))) := by
  have h0 := secPathU_zero_mem (seamBlockPath m ξ) (continuous_seamBlockPath hξ)
    (seamBlockPath_star_mul hξ) (seamBlockPath_mul_star hξ) (fun w => by
      show (Matrix.fromBlocks (seamPath (ePole (m + 1)) 1 (ξ w.1)) 0 0
        (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix (blockEquiv m) (blockEquiv m) = 1
      rw [seamPath_ePole_one, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv])
  have heq : secPathU (seamBlockPath m ξ) (continuous_seamBlockPath hξ)
        (seamBlockPath_star_mul hξ) (seamBlockPath_mul_star hξ) 0
      = sectionBlock (m + 1) (fun v => genU2 (m + 1) (ξ v)) (continuous_genU2_field hξ)
          (genU2_field_star_mul hξ) (genU2_field_mul_star hξ) := by
    refine Subtype.ext (ContinuousMap.ext fun w => ?_)
    show (Matrix.fromBlocks (seamPath (ePole (m + 1)) 0 (ξ w.1)) 0 0
        (1 : Matrix (Fin m) (Fin m) ℂ)).submatrix (blockEquiv m) (blockEquiv m)
      = STW59.matEval w (sectionBlockMat (m + 1) (fun v => genU2 (m + 1) (ξ v))
          (continuous_genU2_field hξ))
    simp only [seamPath_ePole_zero, submatrix_genU_blockEquiv (hξ.mem w.1)
      (ne_neg_one_of_re_eq_zero (hξ.equator w.1)) (ne_one_of_re_eq_zero (hξ.equator w.1)),
      sectionBlockMat, Gen.matEval_fromBlocks, STW59.matEval_zero, STW59.matEval_one,
      matEval_sphereMatAt]
  rw [← heq]
  exact h0

end GenBlock

/-! ## 5. `Aᴴ ⊕ 1` contracts, and the witness -/

section Witness

variable (m : ℕ)

set_option linter.unusedSimpArgs false

/-- The radial contraction of `Aᴴ ⊕ 1` to its value at the centre. -/
def wallBlockPath (t : unitInterval) (w : STW59.Gen.baseX (m + 1) 0) :
    Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) ℂ :=
  Matrix.fromBlocks ((wallA (m + 1) (Nat.succ_pos m)
    ((t : ℝ) • (w.1 : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1))))))ᴴ 0 0 1

theorem norm_smul_sphere_le (t : unitInterval) (v : ↥(STW59.Gen.sphereEven (m + 1))) :
    ‖(t : ℝ) • (v : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1)))‖ ≤ 1 := by
  rw [norm_smul, norm_sphere, mul_one, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  exact t.2.2

theorem continuous_wallBlockPath :
    Continuous fun q : unitInterval × STW59.Gen.baseX (m + 1) 0 => wallBlockPath m q.1 q.2 := by
  have hA : Continuous fun q : unitInterval × STW59.Gen.baseX (m + 1) 0 =>
      wallA (m + 1) (Nat.succ_pos m)
        ((q.1 : ℝ) • (q.2.1 : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1)))) :=
    (isBallUnitary_wallA (m + 1) (Nat.succ_pos m)).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
  exact Continuous.matrix_fromBlocks hA.matrix_conjTranspose continuous_const continuous_const
    continuous_const

theorem wallBlockPath_star_mul (t : unitInterval) (w : STW59.Gen.baseX (m + 1) 0) :
    (wallBlockPath m t w)ᴴ * wallBlockPath m t w = 1 := by
  have h := (isBallUnitary_wallA (m + 1) (Nat.succ_pos m)).mul_star_self _
    (norm_smul_sphere_le m t w.1)
  rw [wallBlockPath, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_conjTranspose, h]
  simp

theorem wallBlockPath_mul_star (t : unitInterval) (w : STW59.Gen.baseX (m + 1) 0) :
    wallBlockPath m t w * (wallBlockPath m t w)ᴴ = 1 := by
  have h := (isBallUnitary_wallA (m + 1) (Nat.succ_pos m)).star_mul_self _
    (norm_smul_sphere_le m t w.1)
  rw [wallBlockPath, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_conjTranspose, h]
  simp

/-- The constant equatorial field at `equatorEmb ε₀`. -/
theorem isEquatorField_const :
    IsEquatorField m fun _ => equatorEmb (m + 1) (Powers.eqBasis (m + 1) (Nat.succ_pos m) 0) where
  continuous := continuous_const
  mem _ := equatorEmb_mem (m + 1) (Powers.norm_eqBasis (m + 1) (Nat.succ_pos m) 0)
  equator _ := re_equatorEmb_last (m + 1) _

/-- The equatorial field `v ↦ equatorEmb v`. -/
theorem isEquatorField_equatorEmb :
    IsEquatorField m fun v : ↥(STW59.Gen.sphereEven (m + 1)) =>
      equatorEmb (m + 1) (v : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1))) where
  continuous := (continuous_equatorEmb (m + 1)).comp continuous_subtype_val
  mem v := equatorEmb_mem (m + 1) (norm_sphere (m + 1) v)
  equator _ := re_equatorEmb_last (m + 1) _

/-- **`Aᴴ ⊕ 1` is null-homotopic in the section algebra over `X₀`.** -/
theorem wallBlock_one_mem :
    secPathU (wallBlockPath m) (continuous_wallBlockPath m) (wallBlockPath_star_mul m)
        (wallBlockPath_mul_star m) 1
      ∈ unitaryComponentOne
          (STW59.SectionAlgebra (STW59.Gen.baseX (m + 1) 0) (Fin (m + 1) ⊕ Fin (m + 1))) := by
  refine secPathU_one_mem _ _ _ _ ?_
  have hC := sectionBlock_genU2_mem (isEquatorField_const m)
  have hprod : secPathU (wallBlockPath m) (continuous_wallBlockPath m) (wallBlockPath_star_mul m)
        (wallBlockPath_mul_star m) 0
      * sectionBlock (m + 1)
          (fun _ => genU2 (m + 1) (equatorEmb (m + 1) (Powers.eqBasis (m + 1) (Nat.succ_pos m) 0)))
          (continuous_genU2_field (isEquatorField_const m))
          (genU2_field_star_mul (isEquatorField_const m))
          (genU2_field_mul_star (isEquatorField_const m)) = 1 := by
    refine Subtype.ext (ContinuousMap.ext fun w => ?_)
    show wallBlockPath m 0 w * STW59.matEval w (sectionBlockMat (m + 1)
      (fun _ => genU2 (m + 1) (equatorEmb (m + 1) (Powers.eqBasis (m + 1) (Nat.succ_pos m) 0)))
      (continuous_genU2_field (isEquatorField_const m))) = 1
    have hA0 : wallA (m + 1) (Nat.succ_pos m)
        (((0 : unitInterval) : ℝ) • (w.1 : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1))))
        = genU2 (m + 1) (equatorEmb (m + 1) (Powers.eqBasis (m + 1) (Nat.succ_pos m) 0)) := by
      rw [Set.Icc.coe_zero, zero_smul]
      exact Powers.ballWall_genSphere_zero (m + 1) (Nat.succ_pos m)
    have hu := genU2_conjTranspose_mul_self (m + 1)
      (equatorEmb_mem (m + 1) (Powers.norm_eqBasis (m + 1) (Nat.succ_pos m) 0))
      (equatorEmb_ne_neg_one (m + 1) _) (equatorEmb_ne_one (m + 1) _)
    simp only [wallBlockPath, hA0, sectionBlockMat, Gen.matEval_fromBlocks, STW59.matEval_zero,
      STW59.matEval_one, matEval_sphereMatAt, Matrix.fromBlocks_multiply, hu, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.fromBlocks_one]
  have hinv := eq_inv_of_mul_eq_one_left hprod
  rw [hinv]
  exact Subgroup.inv_mem _ hC

/-- The witness's block section is the product of the two contracted ones. -/
theorem sectionBlock_topBlock_eq :
    sectionBlock (m + 1) (topBlock (m + 1) (Nat.succ_pos m))
        (continuous_topBlock (m + 1) (Nat.succ_pos m)) (topBlock_star_mul (m + 1) (Nat.succ_pos m))
        (topBlock_mul_star (m + 1) (Nat.succ_pos m))
      = secPathU (wallBlockPath m) (continuous_wallBlockPath m) (wallBlockPath_star_mul m)
          (wallBlockPath_mul_star m) 1
        * sectionBlock (m + 1)
            (fun v => genU2 (m + 1) (equatorEmb (m + 1) (v : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1)))))
            (continuous_genU2_field (isEquatorField_equatorEmb m))
            (genU2_field_star_mul (isEquatorField_equatorEmb m))
            (genU2_field_mul_star (isEquatorField_equatorEmb m)) := by
  refine Subtype.ext (ContinuousMap.ext fun w => ?_)
  show STW59.matEval w (sectionBlockMat (m + 1) (topBlock (m + 1) (Nat.succ_pos m))
      (continuous_topBlock (m + 1) (Nat.succ_pos m)))
    = wallBlockPath m 1 w * STW59.matEval w (sectionBlockMat (m + 1)
      (fun v => genU2 (m + 1) (equatorEmb (m + 1) (v : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1)))))
      (continuous_genU2_field (isEquatorField_equatorEmb m)))
  have hg : genSphere (m + 1) (w.1 : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1)))
      = genU2 (m + 1) (equatorEmb (m + 1) (w.1 : EuclideanSpace ℝ (Fin (2 * (m + 1) + 1)))) := by
    rw [genSphere, norm_sphere, inv_one, one_smul]
  simp only [wallBlockPath, sectionBlockMat, Gen.matEval_fromBlocks, STW59.matEval_zero,
    STW59.matEval_one, matEval_sphereMatAt, Matrix.fromBlocks_multiply, Set.Icc.coe_one, one_smul,
    topBlock, hg, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul]

end Witness

/-! ## 6. The stabilisation input, and the arrow -/

/-- **`diag(ũ ⊕ 1, 1)` is null-homotopic in `M₂(A₀)`, at every rank `n ≥ 1`.** -/
theorem diagWitnessNullHomotopic (n : ℕ) (hn : 0 < n) : DiagWitnessNullHomotopic n hn := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show DiagWitnessNullHomotopic (m + 1) (Nat.succ_pos m)
  refine diagOne_sphereUnitary_mem (topBlock (m + 1) (Nat.succ_pos m))
    (continuous_topBlock (m + 1) (Nat.succ_pos m)) (topBlock_star_mul (m + 1) (Nat.succ_pos m))
    (topBlock_mul_star (m + 1) (Nat.succ_pos m)) ?_
  rw [sectionBlock_topBlock_eq m]
  exact Subgroup.mul_mem _ (wallBlock_one_mem m) (sectionBlock_genU2_mem (isEquatorField_equatorEmb m))

/-- **The arrow `sp-tower` owed**: Lemma 2 at every stage for the degree-`k` sections, whenever a
prime dividing `n` misses `k`, gives the climbed power witness.  No hypothesis beyond `0 < n`. -/
theorem corollary4Powers (n : ℕ) (hn : 0 < n) :
    NinetyNineProblems.Corollary4Powers n (degreeFamily n) :=
  corollary4Powers_of_diag n hn (diagWitnessNullHomotopic n hn)

end

end Gen
end LIX
end GroupApproximation

open GroupApproximation.LIX.Gen

#audit_axioms secPathU_zero_mem
#audit_axioms submatrix_genU_blockEquiv
#audit_axioms sectionBlock_genU2_mem
#audit_axioms wallBlock_one_mem
#audit_axioms diagWitnessNullHomotopic
#audit_axioms corollary4Powers
