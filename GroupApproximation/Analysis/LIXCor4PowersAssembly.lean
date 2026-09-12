import GroupApproximation.Analysis.LIXCor4PowersStage
import GroupApproximation.Analysis.LIXPowersEquator
import GroupApproximation.CharClass.LIXKGenSection
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrong
import GroupApproximation.Meta.AxiomGuard

/-!
# The arrow `Corollary4Powers n b`, for the degree-`k` sections

`Manuscript/NinetyNineProblems/ProblemLIXStrong.lean` names the arrow the C⋆-side owes:

    Corollary4Powers n b :=
      (∀ p, p.Prime → p ∣ n → ∀ k, ¬ p ∣ k → LemmaTwoHoldsForSections n (b k)) →
        ClimbedPowersOutside n .

This file proves it for the family ruled by the lead on 2026-09-11,

    b k j := CharClass.KGen.bVecK (dd := lixDD n j) n (k - 1),

the section of degree `k` (`KGen.psiVec n (k - 1)` has degree `k`, with `k` zeros; `b 0` is never
used, because every prime divides `0`).

## The witness

`ũ = Aᴴ u`, the renormalised seam generator, as the stage-zero unitary `ũ ⊕ 1_{H₀}`:

* `u = Gen.genSphere n`, the rank-`n` seam generator on `S^{2n}`;
* `A = Powers.ballWall (−ε₀) (−ε₁) u`, lane `lix-powers`' ball extension of its wall part.

`A` is continuous and unitary on the whole ball, so it gauges the northern frame over the whole
cap: the gauge of the field is `g x = A (ψ (equatorInv x))`, which on the equator is
`A (ψ (dirPt x))`.  The homotopy `ũ^k ≃ ũ ∘ ψ_{k-1}` is `Powers.exists_homotopy_pow_comp_genSphere`,
and through the equator embedding `ψ_{k-1}` is `KGen.psiVec n (k - 1)`
(`Powers.equatorEmb_joinPow`).

## The one input still named

`Gen.DiagWitnessNullHomotopic n hn : Prop`, `diag(ũ ⊕ 1, 1) ∈ U₀(M₂(A₀))`.  It is the rank-`n` form
of `LIXLemmaSixDiagEnd.hdiag_genUnitary` and it is proved in `Analysis/LIXCor4PowersDiag.lean`;
it is an explicit hypothesis here only so that this file is independent of that plumbing.
-/

namespace GroupApproximation
namespace LIX
namespace Gen

open scoped Matrix ComplexOrder CStarAlgebra

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

set_option linter.unusedSectionVars false

noncomputable section

variable (n : ℕ) (hn : 0 < n)

/-! ## 1. The renormalised generator on `S^{2n}` -/

/-- `A`, the ball extension of the wall part of the seam generator. -/
def wallA (y : EuclideanSpace ℝ (Fin (2 * n + 1))) : Matrix (Fin n) (Fin n) ℂ :=
  Powers.ballWall (-Powers.eqBasis n hn 0) (-Powers.eqBasis n hn 1) (genSphere n) y

theorem isBallUnitary_wallA : Powers.IsBallUnitary (wallA n hn) :=
  Powers.isBallUnitary_ballWall (Powers.norm_neg_eqBasis n hn 0) (Powers.norm_neg_eqBasis n hn 1)
    (Powers.inner_neg_eqBasis_zero_one n hn) (Powers.isSphereUnitary_genSphere n)

theorem continuous_genSphere_sphere :
    Continuous fun v : ↥(STW59.Gen.sphereEven n) =>
      genSphere n (v : EuclideanSpace ℝ (Fin (2 * n + 1))) :=
  (continuousOn_genSphere n).comp_continuous continuous_subtype_val fun v =>
    Powers.sphere_ne_zero (mem_sphere_zero_iff_norm.mp v.2)

/-- **The top block of the witness**, `ũ = Aᴴ u` on `S^{2n}`. -/
def topBlock (v : ↥(STW59.Gen.sphereEven n)) : Matrix (Fin n) (Fin n) ℂ :=
  (wallA n hn (v : EuclideanSpace ℝ (Fin (2 * n + 1))))ᴴ
    * genSphere n (v : EuclideanSpace ℝ (Fin (2 * n + 1)))

theorem continuous_topBlock : Continuous (topBlock n hn) :=
  ((isBallUnitary_wallA n hn).continuous.comp continuous_subtype_val).matrix_conjTranspose.matrix_mul
    (continuous_genSphere_sphere n)

theorem norm_sphere (v : ↥(STW59.Gen.sphereEven n)) :
    ‖(v : EuclideanSpace ℝ (Fin (2 * n + 1)))‖ = 1 :=
  mem_sphere_zero_iff_norm.mp v.2

theorem topBlock_star_mul (v : ↥(STW59.Gen.sphereEven n)) :
    (topBlock n hn v)ᴴ * topBlock n hn v = 1 := by
  have hA := (isBallUnitary_wallA n hn).mul_star_self _ (le_of_eq (norm_sphere n v))
  have hu := genSphere_conjTranspose_mul_self n (Powers.sphere_ne_zero (norm_sphere n v))
  have hA' : ((wallA n hn (v : EuclideanSpace ℝ (Fin (2 * n + 1))))ᴴ)ᴴ
      * (wallA n hn (v : EuclideanSpace ℝ (Fin (2 * n + 1))))ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hA
  exact mul_star_mul_of_unitary hA' hu

theorem topBlock_mul_star (v : ↥(STW59.Gen.sphereEven n)) :
    topBlock n hn v * (topBlock n hn v)ᴴ = 1 := by
  have hA := (isBallUnitary_wallA n hn).star_mul_self _ (le_of_eq (norm_sphere n v))
  have hu := genSphere_mul_conjTranspose n (Powers.sphere_ne_zero (norm_sphere n v))
  have hA' : (wallA n hn (v : EuclideanSpace ℝ (Fin (2 * n + 1))))ᴴ
      * ((wallA n hn (v : EuclideanSpace ℝ (Fin (2 * n + 1))))ᴴ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hA
  exact mul_mul_star_of_unitary hA' hu

/-- **The witness at stage zero**: `ũ ⊕ 1_{H₀}`. -/
def witness : unitary (STW59.Gen.StageAlgebra n 0) :=
  sphereUnitary n (topBlock n hn) (continuous_topBlock n hn) (topBlock_star_mul n hn)
    (topBlock_mul_star n hn)

/-- **The one named input**: the stabilisation of the witness is null-homotopic in `M₂(A₀)`. -/
def DiagWitnessNullHomotopic : Prop :=
  diagOne (witness n hn) ∈ unitaryComponentOne (CStarMat 2 (STW59.Gen.StageAlgebra n 0))

/-! ## 2. The gauge and the pullback -/

/-- `ψ_m` on the equatorial space, for the ruled pair. -/
def psiE (m : ℕ) : EuclideanSpace ℝ (Fin (2 * n + 1)) → EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  Powers.joinPow (Powers.eqBasis n hn 0) (Powers.eqBasis n hn 1) m

theorem isRadialMap_psiE (m : ℕ) : Powers.IsRadialMap (psiE n hn m) :=
  Powers.isRadialMap_joinPow_equator n hn m

/-- The gauge: `A` read at `ψ_m` of the unnormalised equator chart. -/
def gaugeG (m : ℕ) (x : ↥(STW59.Gen.sphereOdd n)) : Matrix (Fin n) (Fin n) ℂ :=
  wallA n hn (psiE n hn m (equatorInv n (x : Fin (n + 1) → ℂ)))

theorem norm_equatorInv_le (x : ↥(STW59.Gen.sphereOdd n)) :
    ‖equatorInv n (x : Fin (n + 1) → ℂ)‖ ≤ 1 := by
  have hsum : (∑ i, ‖(x : Fin (n + 1) → ℂ) i‖ ^ 2 : ℝ) = 1 := x.2
  have h := norm_sq_equatorInv n (x : Fin (n + 1) → ℂ)
  rw [hsum] at h
  nlinarith [norm_nonneg (equatorInv n (x : Fin (n + 1) → ℂ)),
    sq_nonneg (((x : Fin (n + 1) → ℂ) (Fin.last n)).re)]

theorem norm_psiE_equatorInv_le (m : ℕ) (x : ↥(STW59.Gen.sphereOdd n)) :
    ‖psiE n hn m (equatorInv n (x : Fin (n + 1) → ℂ))‖ ≤ 1 := by
  rw [(isRadialMap_psiE n hn m).norm_map]
  exact norm_equatorInv_le n x

theorem continuous_gaugeG (m : ℕ) : Continuous (gaugeG n hn m) :=
  (isBallUnitary_wallA n hn).continuous.comp
    ((isRadialMap_psiE n hn m).continuous.comp
      ((continuous_equatorInv n).comp continuous_subtype_val))

theorem gaugeG_star_mul (m : ℕ) (x : ↥(STW59.Gen.sphereOdd n)) :
    (gaugeG n hn m x)ᴴ * gaugeG n hn m x = 1 :=
  (isBallUnitary_wallA n hn).star_mul_self _ (norm_psiE_equatorInv_le n hn m x)

theorem gaugeG_mul_star (m : ℕ) (x : ↥(STW59.Gen.sphereOdd n)) :
    gaugeG n hn m x * (gaugeG n hn m x)ᴴ = 1 :=
  (isBallUnitary_wallA n hn).mul_star_self _ (norm_psiE_equatorInv_le n hn m x)

/-- The pullback: `KGen.psiVec n m` on `S^{2n+1}`. -/
def psiCap (m : ℕ) (x : ↥(STW59.Gen.sphereOdd n)) : Fin (n + 1) → ℂ :=
  CharClass.KGen.psiVec n m (x : Fin (n + 1) → ℂ)

include hn in
theorem isCapDatum_psiCap (m : ℕ) : IsCapDatum n (psiCap n m) where
  continuous := (CharClass.KGen.continuous_psiVec n m).comp continuous_subtype_val
  mem x := CharClass.KGen.psiVec_mem_unitVectors x.2
  last _ := CharClass.KGen.psiVec_apply_last n m hn _

/-! ## 3. The equator -/

/-- On the equator the cone direction is the unnormalised chart. -/
theorem coe_dirPt_of_capHeight_eq_zero {x : ↥(STW59.Gen.sphereOdd n)} (h : capHeight n x = 0) :
    (dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1))) = equatorInv n (x : Fin (n + 1) → ℂ) := by
  have hsum : (∑ i, ‖(x : Fin (n + 1) → ℂ) i‖ ^ 2 : ℝ) = 1 := x.2
  have hre : ((x : Fin (n + 1) → ℂ) (Fin.last n)).re = 0 := h
  have hn2 : ‖equatorInv n (x : Fin (n + 1) → ℂ)‖ ^ 2 = 1 := by
    rw [norm_sq_equatorInv, hsum, hre]
    ring
  have hn1 : ‖equatorInv n (x : Fin (n + 1) → ℂ)‖ = 1 := by
    nlinarith [norm_nonneg (equatorInv n (x : Fin (n + 1) → ℂ))]
  have hne : equatorInv n (x : Fin (n + 1) → ℂ) ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hn1
    exact zero_ne_one hn1
  rw [coe_dirPt_of_ne hne, hn1, inv_one, one_smul]

/-- **The seam of the `k`-th power, on the equator**: `ũ (ψ_m (dirPt x)) = (g x)ᴴ · genU2 (ψ x)`. -/
theorem normGen_psiE_dirPt (m : ℕ) {x : ↥(STW59.Gen.sphereOdd n)} (h : capHeight n x = 0) :
    Powers.normGen (-Powers.eqBasis n hn 0) (-Powers.eqBasis n hn 1) (genSphere n)
        (psiE n hn m (dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1))))
      = (gaugeG n hn m x)ᴴ * genU2 n (psiCap n m x) := by
  have hd1 : ‖(dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1)))‖ = 1 := norm_sphere n (dirPt n x)
  have hψ1 : ‖psiE n hn m (dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1)))‖ = 1 := by
    rw [(isRadialMap_psiE n hn m).norm_map, hd1]
  rw [Powers.normGen_eq_ballWall_mul hψ1]
  have hgs : genSphere n (psiE n hn m (dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1))))
      = genU2 n (psiCap n m x) := by
    rw [genSphere, hψ1, inv_one, one_smul, psiE, Powers.equatorEmb_joinPow,
      equatorEmb_dirPt h]
    rfl
  rw [hgs, gaugeG, ← coe_dirPt_of_capHeight_eq_zero n h]
  rfl

/-! ## 4. Corollary 4 for the `k`-th power of the witness -/

/-- **Corollary 4 for powers, at stage `j`, for the witness.** -/
theorem witness_pow_notMem (k : ℕ) (hk : 1 ≤ k) (j : ℕ)
    (hlem : LemmaTwoFor n (lixDD n j) (CharClass.KGen.bVecK (dd := lixDD n j) n (k - 1))) :
    unitaryHom ((lixTower n).climbHom (Nat.zero_le j)) (witness n hn ^ k)
      ∉ unitaryComponentOne (STW59.Gen.StageAlgebra n j) := by
  obtain ⟨G, hGc, hG0, hG1, hGu1, hGu2⟩ := Powers.exists_homotopy_pow_comp_genSphere n hn (k - 1)
  have hne : ∀ v : ↥(STW59.Gen.sphereEven n), (v : EuclideanSpace ℝ (Fin (2 * n + 1))) ≠ 0 :=
    fun v => Powers.sphere_ne_zero (norm_sphere n v)
  refine climb_pow_notMem_gauged (isCapDatum_psiCap n hn (k - 1)) (continuous_gaugeG n hn (k - 1))
    (gaugeG_star_mul n hn (k - 1)) (gaugeG_mul_star n hn (k - 1)) (witness n hn)
    (hasSphereShape_sphereStage (topBlock n hn) (continuous_topBlock n hn)) k
    (H := fun t v => G t (v : EuclideanSpace ℝ (Fin (2 * n + 1))))
    (hGc.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      fun r => hne r.2)
    (fun t v => hGu1 t _ (hne v)) (fun t v => hGu2 t _ (hne v)) ?_ ?_ j hlem
  · intro v
    show G 0 (v : EuclideanSpace ℝ (Fin (2 * n + 1))) = topBlock n hn v ^ k
    rw [hG0, Powers.normGen_eq_ballWall_mul (norm_sphere n v), Nat.sub_add_cancel hk]
    rfl
  · intro x hx
    show G 1 (dirPt n x : EuclideanSpace ℝ (Fin (2 * n + 1))) = _
    rw [hG1 _ (norm_sphere n (dirPt n x))]
    exact normGen_psiE_dirPt n hn (k - 1) hx

/-! ## 5. The arrow -/

/-- The degree-`k` family: at exponent `k` the section of degree `k`. -/
def degreeFamily :
    ℕ → ∀ j : ℕ, CharClass.Gen.baseM n (lixDD n j) → Fin (n + 1) → ℂ :=
  fun k j => CharClass.KGen.bVecK (dd := lixDD n j) n (k - 1)

/-- **The arrow, over the named stabilisation input.** -/
theorem corollary4Powers_of_diag (hdiag : DiagWitnessNullHomotopic n hn) :
    NinetyNineProblems.Corollary4Powers n (degreeFamily n) := by
  intro h
  refine ⟨unitaryHom ((lixTower n).limIota 0) (witness n hn),
    diagOne_mem_unitaryComponentOne_map ((lixTower n).limIota 0) hdiag, ?_⟩
  intro p hp hpn k hpk
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (dvd_zero p) hpk
    · exact hpos
  exact lixLimit_pow_notMem n (witness n hn) k fun j =>
    witness_pow_notMem n hn k hk j (h p hp hpn k hpk j)

end

end Gen
end LIX
end GroupApproximation

open GroupApproximation.LIX.Gen

#audit_axioms topBlock_star_mul
#audit_axioms normGen_psiE_dirPt
#audit_axioms witness_pow_notMem
#audit_axioms corollary4Powers_of_diag
