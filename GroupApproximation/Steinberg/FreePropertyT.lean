import GroupApproximation.Steinberg.FiniteControl
import GroupApproximation.Steinberg.RootCharacterValuation
import GroupApproximation.Kazhdan.KazhdanControl

/-!
# Property (T) for Steinberg groups over finite free characteristic-two rings

This module turns the direct Steinberg two-root Fourier estimate into a finite
Kazhdan pair. No canonical projection, kernel-centrality, or unstable K₂
hypothesis is used.
-/

namespace GroupApproximation
namespace SteinbergFreePropertyT

open SteinbergRootCharacterValuation
open FreeAlgebraDegree
open SteinbergRootPlaneFourier
open SteinbergGroup
open scoped commutatorElement

noncomputable section

variable (X : Type*) [Fintype X]

/-- The finite Steinberg control set bounds the moving projection for either
of the two roots in a common-terminal-index plane. -/
theorem norm_columnPlaneMovingProjection_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : SteinbergGroup (Fin 3) (SteinbergRootPlaneFourier.FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) {δ : ℝ} (hδ : 0 < δ)
    (hnear : ∀ s ∈ finiteControlSet X, ‖rho s z - z‖ < δ) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (rootSubgroup i k hik ⊔
          rootSubgroup j k hjk) z‖ ≤
      (6 * Fintype.card X + 6 : ℝ) * δ := by
  classical
  let H : Subgroup (SteinbergGroup (Fin 3) (SteinbergRootPlaneFourier.FreeRing X)) :=
    rootSubgroup i k hik ⊔ rootSubgroup j k hjk
  let w := KazhdanFixedSpace.subgroupMovingProjection rho H z
  have hnearControl (a : A2Root) (q : Option (Fin (Fintype.card X))) :
      ‖rho (finiteControlElement X (a, q)) z - z‖ < δ :=
    hnear _ (finiteControlElement_mem X (a, q))
  have hnormalIJ (a : SteinbergRootPlaneFourier.FreeRing X) :
      SteinbergGroup.x i j hij a ∈ Subgroup.normalizer H := by
    exact x_mem_normalizer_columnPlane X i j k hij hik hjk a
  have hnormalJI (a : SteinbergRootPlaneFourier.FreeRing X) :
      SteinbergGroup.x j i hij.symm a ∈ Subgroup.normalizer H := by
    simpa only [H, sup_comm] using
      x_mem_normalizer_columnPlane X j i k hij.symm hjk hik a
  have hnormalIK (a : SteinbergRootPlaneFourier.FreeRing X) :
      SteinbergGroup.x i k hik a ∈ Subgroup.normalizer H := by
    apply H.le_normalizer
    exact (show rootSubgroup i k hik ≤ H from le_sup_left) ⟨a, rfl⟩
  have hnormalJK (a : SteinbergRootPlaneFourier.FreeRing X) :
      SteinbergGroup.x j k hjk a ∈ Subgroup.normalizer H := by
    apply H.le_normalizer
    exact (show rootSubgroup j k hjk ≤ H from le_sup_right) ⟨a, rfl⟩
  have hmove_le (g : SteinbergGroup (Fin 3) (SteinbergRootPlaneFourier.FreeRing X))
      (hg : g ∈ Subgroup.normalizer H) :
      ‖rho g w - w‖ ≤ ‖rho g z - z‖ := by
    exact
      KazhdanFixedSpace.norm_subgroupMovingProjection_displacement_le_of_mem_normalizer
        rho H hg z
  have hwIK : ‖rho (SteinbergGroup.x i k hik 1) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalIK 1)).trans
      (hnearControl ⟨(i, k), hik⟩ none).le
  have hwJK : ‖rho (SteinbergGroup.x j k hjk 1) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalJK 1)).trans
      (hnearControl ⟨(j, k), hjk⟩ none).le
  have hwIJUnit : ‖rho (SteinbergGroup.x i j hij 1) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalIJ 1)).trans
      (hnearControl ⟨(i, j), hij⟩ none).le
  have hwJIUnit : ‖rho (SteinbergGroup.x j i hij.symm 1) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalJI 1)).trans
      (hnearControl ⟨(j, i), hij.symm⟩ none).le
  have hwIJ (q : Fin (Fintype.card X)) :
      ‖rho (SteinbergGroup.x i j hij
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalIJ _)).trans
      (by
        simpa [finiteControlElement, finiteControlCoefficient,
          finiteGeneratorEnumeration, generatorEnumeration] using
          (hnearControl ⟨(i, j), hij⟩ (some q)).le)
  have hwJI (q : Fin (Fintype.card X)) :
      ‖rho (SteinbergGroup.x j i hij.symm
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalJI _)).trans
      (by
        simpa [finiteControlElement, finiteControlCoefficient,
          finiteGeneratorEnumeration, generatorEnumeration] using
          (hnearControl ⟨(j, i), hij.symm⟩ (some q)).le)
  have hsumIJ :
      (∑ q : Fin (Fintype.card X),
          2 * ‖w‖ * ‖rho (SteinbergGroup.x i j hij
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) w - w‖) ≤
        Fintype.card X * (2 * ‖w‖ * δ) := by
    calc
      _ ≤ ∑ _q : Fin (Fintype.card X), 2 * ‖w‖ * δ := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hwIJ q)
          (mul_nonneg (by norm_num) (norm_nonneg w))
      _ = Fintype.card X * (2 * ‖w‖ * δ) := by simp
  have hsumJI :
      (∑ q : Fin (Fintype.card X),
          2 * ‖w‖ * ‖rho (SteinbergGroup.x j i hij.symm
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) w - w‖) ≤
        Fintype.card X * (2 * ‖w‖ * δ) := by
    calc
      _ ≤ ∑ _q : Fin (Fintype.card X), 2 * ‖w‖ * δ := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hwJI q)
          (mul_nonneg (by norm_num) (norm_nonneg w))
      _ = Fintype.card X * (2 * ‖w‖ * δ) := by simp
  have hwProjection :
      KazhdanFixedSpace.subgroupMovingProjection rho H w = w := by
    let U := KazhdanFixedSpace.fixedSubspace rho H
    letI : CompleteSpace U :=
      (KazhdanFixedSpace.isClosed_fixedSubspace rho H).completeSpace_coe
    change Uᗮ.starProjection w = w
    exact Uᗮ.starProjection_eq_self_iff.mpr
      (KazhdanFixedSpace.subgroupMovingProjection_mem rho H z)
  have hestimate :=
    norm_joinRootMovingProjection_sq_le_explicit_errors
      X i j k hij hik hjk rho w
  change ‖KazhdanFixedSpace.subgroupMovingProjection rho H w‖ ^ 2 ≤ _ at hestimate
  rw [hwProjection] at hestimate
  have hwIKsq :
      ‖rho (SteinbergGroup.x i k hik 1) w - w‖ ^ 2 ≤ δ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hδ.le).2 hwIK
  have hwJKsq :
      ‖rho (SteinbergGroup.x j k hjk 1) w - w‖ ^ 2 ≤ δ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hδ.le).2 hwJK
  have hwIJUnitTerm :
      2 * ‖w‖ * ‖rho (SteinbergGroup.x i j hij 1) w - w‖ ≤
        2 * ‖w‖ * δ :=
    mul_le_mul_of_nonneg_left hwIJUnit
      (mul_nonneg (by norm_num) (norm_nonneg w))
  have hwJIUnitTerm :
      2 * ‖w‖ * ‖rho (SteinbergGroup.x j i hij.symm 1) w - w‖ ≤
        2 * ‖w‖ * δ :=
    mul_le_mul_of_nonneg_left hwJIUnit
      (mul_nonneg (by norm_num) (norm_nonneg w))
  have hquadratic :
      ‖w‖ ^ 2 ≤ 2 * δ ^ 2 +
        (6 * Fintype.card X + 4 : ℝ) * ‖w‖ * δ := by
    have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
    nlinarith
  change ‖w‖ ≤ (6 * Fintype.card X + 6 : ℝ) * δ
  have hC : (1 : ℝ) ≤ 6 * Fintype.card X + 6 := by
    have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
    linarith
  by_cases hwδ : ‖w‖ ≤ δ
  · exact hwδ.trans (le_mul_of_one_le_left hδ.le hC)
  · have hδw : δ ≤ ‖w‖ := le_of_lt (lt_of_not_ge hwδ)
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hδ0 : 0 ≤ δ := hδ.le
    have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
    nlinarith

/-- The finite Steinberg control set uniformly controls displacement by the
union of all six root subgroups. -/
theorem finiteControlSet_controls_rootSet :
    ControlsSubsetDisplacement
      (SteinbergGroup (Fin 3) (SteinbergRootPlaneFourier.FreeRing X))
      (finiteControlSet X)
      (a2System (R := SteinbergRootPlaneFourier.FreeRing X)).rootSet
      (12 * Fintype.card X + 13 : ℝ) := by
  intro E _ _ _ rho z _hz δ hδ hnear g hg
  obtain ⟨a, hga⟩ :=
    ((a2System (R := SteinbergRootPlaneFourier.FreeRing X)).mem_rootSet_iff g).mp hg
  let i := a.1.1
  let k := a.1.2
  let j := a2ThirdIndex i k
  have hij : i ≠ j := (a2ThirdIndex_ne_left i k a.2).symm
  have hjk : j ≠ k := a2ThirdIndex_ne_right i k a.2
  let H : Subgroup (SteinbergGroup (Fin 3) (SteinbergRootPlaneFourier.FreeRing X)) :=
    rootSubgroup i k a.2 ⊔ rootSubgroup j k hjk
  have hprojection := norm_columnPlaneMovingProjection_le
    X i j k hij a.2 hjk rho z hδ hnear
  have hgH : g ∈ H := by
    exact (show rootSubgroup i k a.2 ≤ H from le_sup_left) hga
  have hdisplacement :=
    KazhdanFixedSpace.norm_displacement_le_two_mul_norm_subgroupMovingProjection_of_mem
      rho H hgH z
  calc
    ‖rho g z - z‖ ≤
        2 * ‖KazhdanFixedSpace.subgroupMovingProjection rho H z‖ :=
      hdisplacement
    _ ≤ 2 * ((6 * Fintype.card X + 6 : ℝ) * δ) := by
      exact mul_le_mul_of_nonneg_left hprojection (by norm_num)
    _ < (12 * Fintype.card X + 13 : ℝ) * δ := by
      have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
      nlinarith

/-- The explicit control set is a genuine finite Kazhdan pair. -/
theorem finiteControlSet_isKazhdanPair :
    ∃ epsilon : ℝ,
      IsKazhdanPair (SteinbergGroup (Fin 3) (SteinbergRootPlaneFourier.FreeRing X))
        (finiteControlSet X) epsilon := by
  obtain ⟨kappa, hkappa⟩ :=
    SteinbergGroup.exists_rootSet_isKazhdan
      (SteinbergRootPlaneFourier.FreeRing X) 2 (by omega)
  let C : ℝ := 12 * Fintype.card X + 13
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  exact ⟨kappa / (2 * C),
    IsKazhdanSubset.to_pair_of_controls hkappa hC
      (finiteControlSet_controls_rootSet X)⟩

/-- Steinberg rank three over the finite free characteristic-two algebra has
Kazhdan's property `(T)`. -/
theorem freeSteinberg_hasKazhdanPropertyT :
    HasKazhdanPropertyT (SteinbergGroup (Fin 3) (SteinbergRootPlaneFourier.FreeRing X)) := by
  obtain ⟨epsilon, hpair⟩ := finiteControlSet_isKazhdanPair X
  exact ⟨finiteControlSet X, epsilon, hpair⟩

end
end SteinbergFreePropertyT
end GroupApproximation
