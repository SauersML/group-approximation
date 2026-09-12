import GroupApproximation.Kazhdan.KazhdanOrthogonal
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.KazhdanGenerators
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The Kazhdan projection as a uniform orbit-average limit

For a Kazhdan pair contained in a finite set `S` containing the identity, the
uniform orbit average contracts the orthogonal complement of the invariant
vectors by a fixed factor `c < 1`. Consequently its powers converge in
operator norm, uniformly over every orthogonal representation, to the
orthogonal projection onto the invariant vectors.

This is the constructive form of the central Kazhdan projection needed by the
weak-MF corner argument: the approximating operators are explicit finite
linear combinations of group elements, so the same polynomials can be
evaluated in finite matrix microstates.
-/

namespace GroupApproximation
namespace KazhdanProjection

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Property `(T)` supplies one finite symmetric generating Kazhdan set,
containing the identity, with tolerance in `(0,1]`.  This is the form whose
matrix orbit average is asymptotically self-adjoint and whose corner commutes
with every group element. -/
theorem HasKazhdanPropertyT.exists_symmetric_generating_pair
    (hT : HasKazhdanPropertyT.{u, u} G) :
    ∃ S : Finset G, ∃ ε : ℝ,
      1 ∈ S ∧ (∀ g ∈ S, g⁻¹ ∈ S) ∧
      Subgroup.closure (S : Set G) = ⊤ ∧ 0 < ε ∧ ε ≤ 1 ∧
      IsKazhdanPair.{u, u} G S ε := by
  obtain ⟨S, hone, hsymm, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset G hT
  obtain ⟨a, ha⟩ := KazhdanGenerators.exists_pair_on_generators
    hT S hsymm hgen
  let ε : ℝ := min a 1
  have hεpos : 0 < ε := lt_min ha.1 zero_lt_one
  have hεa : ε ≤ a := min_le_left _ _
  have hεone : ε ≤ 1 := min_le_right _ _
  exact ⟨S, ε, hone, hsymm, hgen, hεpos, hεone,
    IsKazhdanPair.shrink ha hεpos hεa⟩

/-- The orbit average bundled as a continuous linear operator. -/
noncomputable def averageOperator (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : E →L[ℝ] E :=
  ((S.card : ℝ)⁻¹) •
    ∑ g ∈ S, (ρ g).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem averageOperator_apply (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    averageOperator S ρ x = IsKazhdanPair.orbitAverage S ρ x := by
  classical
  simp [averageOperator, IsKazhdanPair.orbitAverage]

/-- The orbit average fixes every invariant vector. -/
theorem averageOperator_apply_of_invariant (S : Finset G)
    (hone : 1 ∈ S) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E}
    (hx : x ∈ KazhdanOrthogonal.invariantSubmodule ρ) :
    averageOperator S ρ x = x := by
  classical
  have hfix : ∀ g : G, ρ g x = x :=
    (KazhdanOrthogonal.mem_invariantSubmodule ρ x).mp hx
  rw [averageOperator_apply, IsKazhdanPair.orbitAverage]
  simp_rw [hfix]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, hone⟩)
  simp [← Nat.cast_smul_eq_nsmul ℝ, hcard]

/-- The orbit average preserves the orthogonal complement of the invariant
subspace. -/
theorem averageOperator_mem_orthogonal (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E}
    (hx : x ∈ (KazhdanOrthogonal.invariantSubmodule ρ)ᗮ) :
    averageOperator S ρ x ∈
      (KazhdanOrthogonal.invariantSubmodule ρ)ᗮ := by
  classical
  rw [averageOperator_apply, IsKazhdanPair.orbitAverage]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g hg ↦
    KazhdanOrthogonal.map_mem_orthogonal ρ g hx)

/-- Iterated orbit averaging contracts the moving subspace geometrically. -/
theorem norm_averageOperator_pow_le [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E}
    (hx : x ∈ (KazhdanOrthogonal.invariantSubmodule ρ)ᗮ) (k : ℕ) :
    ‖(averageOperator S ρ ^ k) x‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ k * ‖x‖ := by
  let c : ℝ := 1 - ε ^ 2 / (4 * S.card)
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hden : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hcard
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hcardNat
    nlinarith
  have hc : 0 ≤ c := by
    dsimp [c]
    rw [sub_nonneg, div_le_one hden]
    exact hεsq.trans hdenOne
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      have hxk : (averageOperator S ρ ^ k) x ∈
          (KazhdanOrthogonal.invariantSubmodule ρ)ᗮ := by
        clear ih
        induction k with
        | zero => simpa using hx
        | succ k hk =>
            rw [pow_succ', mul_apply_eq_comp]
            exact averageOperator_mem_orthogonal S ρ hk
      calc
        ‖averageOperator S ρ ((averageOperator S ρ ^ k) x)‖ ≤
            c * ‖(averageOperator S ρ ^ k) x‖ := by
          rw [averageOperator_apply]
          exact KazhdanOrthogonal.norm_orbitAverage_le_of_mem_orthogonal
            hQ S hQS hone hεone ρ hxk
        _ ≤ c * (c ^ k * ‖x‖) := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (k + 1) * ‖x‖ := by rw [pow_succ]; ring

/-- The `k`-th orbit-average power agrees with the identity on the invariant
subspace. -/
theorem averageOperator_pow_apply_of_invariant (S : Finset G)
    (hone : 1 ∈ S) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E}
    (hx : x ∈ KazhdanOrthogonal.invariantSubmodule ρ) (k : ℕ) :
    (averageOperator S ρ ^ k) x = x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih]
      exact averageOperator_apply_of_invariant S hone ρ hx

/-- The invariant subspace of an orthogonal representation is closed. -/
theorem isClosed_invariantSubmodule (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    IsClosed (KazhdanOrthogonal.invariantSubmodule ρ : Set E) := by
  rw [show (KazhdanOrthogonal.invariantSubmodule ρ : Set E) =
      ⋂ g : G, {x : E | ρ g x = x} by
    ext x
    simp [KazhdanOrthogonal.mem_invariantSubmodule]]
  exact isClosed_iInter fun g ↦ isClosed_eq (ρ g).continuous continuous_id

/-- Orthogonal projection onto the globally invariant vectors. -/
noncomputable def invariantProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : E →L[ℝ] E := by
  let U := KazhdanOrthogonal.invariantSubmodule ρ
  letI : CompleteSpace U := (isClosed_invariantSubmodule ρ).completeSpace_coe
  exact U.starProjection

/-- **Uniform Kazhdan projection estimate.** Powers of the explicit orbit
average converge in operator norm to the orthogonal projection onto invariant
vectors, with a representation-independent geometric rate. -/
theorem norm_averageOperator_pow_sub_projection_le [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (k : ℕ) :
    ‖averageOperator S ρ ^ k -
        invariantProjection ρ‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ k := by
  let U := KazhdanOrthogonal.invariantSubmodule ρ
  let c : ℝ := 1 - ε ^ 2 / (4 * S.card)
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hden : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hcard
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hcardNat
    nlinarith
  have hc : 0 ≤ c := by
    dsimp [c]
    rw [sub_nonneg, div_le_one hden]
    exact hεsq.trans hdenOne
  letI : CompleteSpace U := (isClosed_invariantSubmodule ρ).completeSpace_coe
  change ‖averageOperator S ρ ^ k - U.starProjection‖ ≤ c ^ k
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hc k) fun x ↦ ?_
  let p : E := U.starProjection x
  let w : E := Uᗮ.starProjection x
  have hp : p ∈ U := U.starProjection_apply_mem x
  have hw : w ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  have hxsplit : p + w = x := U.starProjection_add_starProjection_orthogonal x
  have hpowp : (averageOperator S ρ ^ k) p = p :=
    averageOperator_pow_apply_of_invariant S hone ρ hp k
  have hproj : U.starProjection x = p := rfl
  have heq : (averageOperator S ρ ^ k - U.starProjection) x =
      (averageOperator S ρ ^ k) w := by
    rw [sub_apply, hproj]
    conv_lhs =>
      congr
      · rw [← hxsplit, map_add, hpowp]
    abel
  rw [heq]
  calc
    ‖(averageOperator S ρ ^ k) w‖ ≤ c ^ k * ‖w‖ :=
      norm_averageOperator_pow_le hQ S hQS hone hεone ρ hw k
    _ ≤ c ^ k * ‖x‖ := mul_le_mul_of_nonneg_left
      (Uᗮ.norm_starProjection_apply_le x) (pow_nonneg hc k)

end KazhdanProjection
end GroupApproximation
