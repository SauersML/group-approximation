import GroupApproximation.Analysis.StarStrongBlockModel

/-!
# The block family on `ℓ²`: `EllTwoBlockFamilyStatement`, discharged

`Analysis/StarStrongBlockModel` reduced Shulman's algebra `𝒟` — and the
isometry data of `Analysis/ArvesonBHTarget` — to one concrete input: isometries
`Jₙ : ℂⁿ → ℓ²` with `Jₙ* Jₙ = 1`, `‖Jₙ‖ ≤ 1` and `Jₙ Jₙ* → 1` strongly.  This
module builds them.

`Jₙ v = ∑_{i < n} single(i, vᵢ)` is a *finite* sum of point masses, so no
`Memℓp` proof is needed anywhere: each summand is already an element of `ℓ²`,
and `lp` is a module.  From there:

* the coordinates of `Jₙ v` come from `lp.evalCLM`, which is a continuous linear
  map, so `map_sum` gives the coordinates of the sum for free;
* `⟪Jₙ v, Jₙ u⟫ = ⟪v, u⟫` is the double sum `∑ᵢ ∑ⱼ ⟪single(i,vᵢ), single(j,uⱼ)⟫`
  with its off-diagonal terms killed by `lp.single_apply_ne`;
* `Jₙ* Jₙ = 1` and `‖Jₙ‖ ≤ 1` follow from that identity, so neither needs the
  norm of `Jₙ v` to be computed in advance — the crude bound `‖Jₙ v‖ ≤ n ‖v‖`,
  enough to make `Jₙ` continuous, is the triangle inequality;
* `Jₙ Jₙ* w` is the `n`-th partial sum of `∑ᵢ single(i, wᵢ)`, and
  `lp.hasSum_single` says that sum is `w`, so `HasSum.tendsto_sum_nat` gives the
  strong convergence.  This is the only analytic step, and it is one line.

## Confidence

Authored while builds are suspended, so nothing here has been elaborated.  Every
`lp` name it uses is attested elsewhere in this repository —
`lp.evalCLM` (whose application is `rfl`, as `Analysis/UniformRoeAlgebra` uses
it), `lp.ext`, `lp.coeFn_add`, `lp.coeFn_smul`, `lp.single_apply_self`,
`lp.single_apply_ne` (its hypothesis is `x ≠ i`, the evaluation point against
the index), `lp.norm_single`, `lp.inner_single_left` (the single on the *left*),
`lp.hasSum_single`, `PiLp.inner_apply`, `EuclideanSpace.norm_eq`.

An earlier header of `Analysis/StarStrongBlockModel` claimed `lp.single_add`,
`lp.inner_single_left` and `lp.hasSum_single` had no precedent here.  Two of
those three are used in half a dozen modules of this repository, and the third,
`lp.single_add`, is in Mathlib at the pinned revision along with
`lp.single_smul` — it was only absent from *this* repository.  Both wrappers
below are now one line each.  The lesson is that "no precedent" was a claim
about a search of the repository, and the library was never searched at all.

The names carrying real risk, and so the first places a build should look, are
`RCLike.inner_apply` (used once, in `complex_inner_eq`, to read `⟪a, b⟫_ℂ` as
`conj a * b`), `ext_inner_left`, `HasSum.tendsto_sum_nat` and
`Fin.sum_univ_eq_sum_range`.  One further point is structural rather than
nominal: `WithLp` is a structure in this Mathlib, not a type synonym, so
`blockRestrict` builds its element of `EuclideanSpace ℂ (Fin n)` through
`WithLp.toLp 2`, the way `Analysis/VectorHilbertUltraproduct`'s `evec` does.
Reading a coordinate `v i` is unaffected — it is the structure projection
followed by application — and `blockRestrict_apply` is still `rfl`, as
`evec_apply` is there.

This module is in the root import list.
-/

namespace GroupApproximation
namespace StarStrong

open Filter Topology

open scoped InnerProductSpace

noncomputable section

/-- `ℓ²(ℕ)`, the Hilbert space the printed block model acts on. -/
abbrev EllTwo : Type := lp (fun _ : ℕ ↦ ℂ) 2

/-! ## Coordinates -/

/-- Coordinates of a finite sum, through the evaluation map, which is a
continuous linear map. -/
theorem ellTwo_sum_apply {ι : Type} (s : Finset ι) (f : ι → EllTwo) (m : ℕ) :
    (∑ i ∈ s, f i) m = ∑ i ∈ s, (f i) m :=
  map_sum (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 2 m) f s

/-- `lp.single` is additive in its value.  The ascription to `EllTwo` is what
fixes the family `E`: without an expected type the elaborator leaves it a
metavariable and cannot solve `?E i =?= ℂ`. -/
theorem ellTwo_single_add (i : ℕ) (a b : ℂ) :
    (lp.single 2 i (a + b) : EllTwo)
      = lp.single 2 i a + lp.single 2 i b :=
  lp.single_add (E := fun _ : ℕ ↦ ℂ) 2 i a b

/-- `lp.single` is homogeneous in its value.  `c * a` is `c • a` for `ℂ`, so
this is the library's `lp.single_smul`. -/
theorem ellTwo_single_smul (i : ℕ) (c a : ℂ) :
    (lp.single 2 i (c * a) : EllTwo) = c • lp.single 2 i a := by
  rw [← smul_eq_mul]
  exact lp.single_smul (E := fun _ : ℕ ↦ ℂ) 2 i c a

/-! ## The inclusion of the first `n` coordinates -/

/-- `ℂⁿ → ℓ²`, as a linear map: a finite sum of point masses, so no membership
proof is needed. -/
def blockInclLinear (n : ℕ) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EllTwo where
  toFun v := ∑ i : Fin n, lp.single 2 (i : ℕ) (v i)
  map_add' v w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ ellTwo_single_add (i : ℕ) (v i) (w i)
  map_smul' c v := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ ellTwo_single_smul (i : ℕ) c (v i)

@[simp] theorem blockInclLinear_apply (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    blockInclLinear n v = ∑ i : Fin n, lp.single 2 (i : ℕ) (v i) := rfl

/-- A coordinate of `Jₙ v` inside the block. -/
theorem blockInclLinear_coord (n : ℕ) (v : EuclideanSpace ℂ (Fin n))
    (j : Fin n) : (blockInclLinear n v) (j : ℕ) = v j := by
  rw [blockInclLinear_apply, ellTwo_sum_apply]
  rw [Finset.sum_eq_single j]
  · exact lp.single_apply_self (E := fun _ : ℕ ↦ ℂ) 2 (j : ℕ) (v j)
  · intro i _ hij
    refine lp.single_apply_ne (E := fun _ : ℕ ↦ ℂ) 2 (i : ℕ) (v i) ?_
    intro hcoe
    exact hij (Fin.ext hcoe.symm)
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Every coordinate of a Euclidean vector is bounded by its norm. -/
theorem euclidean_coord_norm_le {n : ℕ} (v : EuclideanSpace ℂ (Fin n))
    (i : Fin n) : ‖v i‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ‖v i‖ ^ 2 ≤ ∑ j : Fin n, ‖v j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin n ↦ ‖v j‖ ^ 2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
  have hsq : Real.sqrt (‖v i‖ ^ 2) ≤ Real.sqrt (∑ j : Fin n, ‖v j‖ ^ 2) :=
    Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg (v i))] at hsq

/-- The crude bound that makes the inclusion continuous.  It is not sharp — the
inclusion is isometric — but sharpness is cheaper to prove afterwards, from the
inner-product identity. -/
theorem norm_blockInclLinear_le (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    ‖blockInclLinear n v‖ ≤ (n : ℝ) * ‖v‖ := by
  rw [blockInclLinear_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i : Fin n,
      ‖(lp.single 2 (i : ℕ) (v i) : EllTwo)‖ ≤ ‖v‖ := by
    intro i
    rw [lp.norm_single (by norm_num)]
    exact euclidean_coord_norm_le v i
  refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The inclusion of the first `n` coordinates**, as a continuous linear
map. -/
def blockIncl (n : ℕ) : EuclideanSpace ℂ (Fin n) →L[ℂ] EllTwo :=
  LinearMap.mkContinuous (blockInclLinear n) (n : ℝ) (norm_blockInclLinear_le n)

@[simp] theorem blockIncl_apply (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    blockIncl n v = ∑ i : Fin n, lp.single 2 (i : ℕ) (v i) := rfl

theorem blockIncl_coord (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (blockIncl n v) (j : ℕ) = v j :=
  blockInclLinear_coord n v j

/-! ## The inclusion is isometric -/

/-- The scalar inner product of `ℂ`, in the shape `lp.inner_single_left`
produces. -/
theorem complex_inner_eq (a b : ℂ) : ⟪a, b⟫_ℂ = (starRingEnd ℂ) a * b :=
  (RCLike.inner_apply a b).trans (mul_comm _ _)

/-- **`Jₙ` preserves inner products.**  The double sum collapses to its
diagonal, the off-diagonal terms vanishing because a point mass is supported at
one coordinate. -/
theorem inner_blockIncl (n : ℕ) (v u : EuclideanSpace ℂ (Fin n)) :
    ⟪blockIncl n v, blockIncl n u⟫_ℂ = ⟪v, u⟫_ℂ := by
  rw [blockIncl_apply, sum_inner]
  have hterm : ∀ i : Fin n,
      ⟪lp.single 2 (i : ℕ) (v i), blockIncl n u⟫_ℂ = ⟪v i, u i⟫_ℂ := by
    intro i
    rw [lp.inner_single_left, blockIncl_coord, complex_inner_eq]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, PiLp.inner_apply]

/-- **`Jₙ* Jₙ = 1`.** -/
theorem adjoint_blockIncl_blockIncl (n : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    (ContinuousLinearMap.adjoint (blockIncl n)) (blockIncl n v) = v := by
  refine ext_inner_left ℂ fun u ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_blockIncl n u v

/-- `Jₙ` is a contraction. -/
theorem norm_blockIncl_le_one (n : ℕ) : ‖blockIncl n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  have hsq : ‖blockIncl n v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h1 : ⟪blockIncl n v, blockIncl n v⟫_ℂ = ⟪v, v⟫_ℂ :=
      inner_blockIncl n v v
    have h2 : ‖blockIncl n v‖ ^ 2 = ‖⟪blockIncl n v, blockIncl n v⟫_ℂ‖ := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
      simp
    have h3 : ‖v‖ ^ 2 = ‖⟪v, v⟫_ℂ‖ := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
      simp
    rw [h2, h3, h1]
  have hnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  nlinarith [hsq, norm_nonneg (blockIncl n v), hnn]

/-! ## The range projections converge strongly to the identity -/

/-- The restriction of an `ℓ²` vector to its first `n` coordinates. -/
def blockRestrict (n : ℕ) (w : EllTwo) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i : Fin n ↦ w (i : ℕ)

@[simp] theorem blockRestrict_apply (n : ℕ) (w : EllTwo) (i : Fin n) :
    blockRestrict n w i = w (i : ℕ) := rfl

/-- **`Jₙ*` is the restriction to the first `n` coordinates.**  Both sides pair
with an arbitrary `u` to the same finite sum `∑ᵢ conj(uᵢ) wᵢ`. -/
theorem adjoint_blockIncl_apply (n : ℕ) (w : EllTwo) :
    (ContinuousLinearMap.adjoint (blockIncl n)) w = blockRestrict n w := by
  refine ext_inner_left ℂ fun u ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_right, blockIncl_apply, sum_inner,
    PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lp.inner_single_left, blockRestrict_apply]

/-- `Jₙ Jₙ* w` is the `n`-th partial sum of the point-mass expansion of `w`. -/
theorem blockIncl_adjoint_apply (n : ℕ) (w : EllTwo) :
    blockIncl n ((ContinuousLinearMap.adjoint (blockIncl n)) w)
      = ∑ i ∈ Finset.range n, lp.single 2 i (w i) := by
  rw [adjoint_blockIncl_apply, blockIncl_apply]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ lp.single 2 i (w i)) n

/-- **The range projections converge strongly to `1`.**  This is
`lp.hasSum_single` read along the partial sums. -/
theorem tendsto_blockIncl_adjoint (w : EllTwo) :
    Tendsto (fun n ↦ blockIncl n
      ((ContinuousLinearMap.adjoint (blockIncl n)) w)) atTop (𝓝 w) := by
  have hsum : HasSum (fun i : ℕ ↦ lp.single 2 i (w i)) w :=
    lp.hasSum_single (by norm_num) w
  have h := hsum.tendsto_sum_nat
  refine h.congr fun n ↦ ?_
  exact (blockIncl_adjoint_apply n w).symm

/-! ## The statement, discharged -/

/-- **`EllTwoBlockFamilyStatement`, proved.** -/
theorem ellTwoBlockFamily : EllTwoBlockFamilyStatement :=
  ⟨blockIncl, adjoint_blockIncl_blockIncl, norm_blockIncl_le_one,
    tendsto_blockIncl_adjoint⟩

end

end StarStrong
end GroupApproximation
