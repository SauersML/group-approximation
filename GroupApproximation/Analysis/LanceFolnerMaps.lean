import GroupApproximation.Analysis.CStarChoiMap
import GroupApproximation.Analysis.CStarUnitalCPContractive
import GroupApproximation.Analysis.LanceBlockOperator
import GroupApproximation.Analysis.ReducedGroupCStarSpan

/-!
# The two Følner maps

The forward half of Lance's theorem --- an amenable group has a nuclear
reduced C⋆-algebra --- is a completely positive factorization of the
identity of `C⋆_λ(G)` through `B(ℂᵏ)`, built from a Følner set.  This file
constructs the two maps and proves everything about them except the
estimate that closes the factorization, which is `Analysis/LanceAmenableNuclear`.

Fix an injective `e : Fin k → G` (an enumeration of a finite set `F ⊆ G`)
and a tuple `c : Fin k → ℂ` of amplitudes.

* `folnerIncl e : ℂᵏ → ℓ²(G)` sends the standard basis to the point masses
  `δ_{e i}`.  It is an isometry (`inner_folnerIncl`), which is where
  injectivity of `e` is used and the only place it is used.
* `folnerDown e a = J⋆ a J` is the compression to those `k` coordinates.
  Its matrix entries are `⟪δ_{e p}, a δ_{e q}⟫`; it is unital because `J` is
  an isometry, and completely positive by the block-operator bridge of
  `Analysis/LanceBlockOperator`.
* `folnerUp e c` is the Choi-type map of the tuple `b_p = c_p λ_{e p}⋆`, so
  `Analysis/CStarChoiMap` makes it completely positive outright.  It is
  unital exactly when `∑ |c_p|² = 1`.

The composite is computed in `folnerUp_folnerDown_leftRegular`: on a
translation it is a **scalar multiple of that same translation**, the scalar
being the Følner overlap `∑_{q : g·e q ∈ F} c̄_{p(q)} c_q`.  That is the
whole content of the construction; the estimate is then arithmetic.

Both maps are contractive by `IsCompletelyPositive.norm_apply_le_of_unital`,
so nothing here needs a norm bound on an amplification.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finset ReducedGroupCStarTrace GroupVonNeumann
open scoped Classical

noncomputable section

universe u

variable {G : Type u} [Group G]

/-! ## The inclusion of `ℂᵏ` as `k` point masses -/

/-- `ℂᵏ → ℓ²(G)`, sending the `i`-th standard basis vector to `δ_{e i}`. -/
omit [Group G] in
theorem norm_single_one (g : G) :
    ‖(lp.single 2 g (1 : ℂ) : GroupHilbert G)‖ = 1 := by
  rw [lp.norm_single (by norm_num), norm_one]

/-- `ℂ → ℓ²(G)`, `z ↦ z · δ_g`, as a continuous linear map. -/
def deltaLine (g : G) : ℂ →L[ℂ] GroupHilbert G :=
  (LinearIsometry.toSpanSingleton ℂ (GroupHilbert G)
    (norm_single_one g)).toContinuousLinearMap

theorem deltaLine_apply (g : G) (z : ℂ) :
    deltaLine g z = z • (lp.single 2 g (1 : ℂ) : GroupHilbert G) := rfl

def folnerIncl {k : ℕ} (e : Fin k → G) :
    EuclideanSpace ℂ (Fin k) →L[ℂ] GroupHilbert G :=
  ∑ i : Fin k,
    (deltaLine (e i)).comp
      (innerSL ℂ (EuclideanSpace.single i (1 : ℂ) :
        EuclideanSpace ℂ (Fin k)))

theorem folnerIncl_apply {k : ℕ} (e : Fin k → G)
    (v : EuclideanSpace ℂ (Fin k)) :
    folnerIncl e v
      = ∑ i : Fin k, v i • (lp.single 2 (e i) (1 : ℂ) : GroupHilbert G) := by
  rw [folnerIncl, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.comp_apply, deltaLine_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul]

/-- The point masses are orthonormal. -/
omit [Group G] in
theorem inner_single_single (s t : G) :
    ⟪(lp.single 2 s (1 : ℂ) : GroupHilbert G),
      (lp.single 2 t (1 : ℂ) : GroupHilbert G)⟫_ℂ = if s = t then 1 else 0 := by
  classical
  rw [lp.inner_single_left]
  by_cases h : s = t
  · subst h
    rw [lp.single_apply_self, if_pos rfl]
    simp
  · rw [lp.single_apply_ne _ _ _ h, if_neg h]
    simp

/-- **The inclusion is an isometry** when `e` is injective. -/
theorem inner_folnerIncl {k : ℕ} {e : Fin k → G} (he : Function.Injective e)
    (u v : EuclideanSpace ℂ (Fin k)) :
    ⟪folnerIncl e u, folnerIncl e v⟫_ℂ = ⟪u, v⟫_ℂ := by
  classical
  rw [folnerIncl_apply, folnerIncl_apply, sum_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_sum]
  have hterm : ∀ j : Fin k,
      ⟪u i • (lp.single 2 (e i) (1 : ℂ) : GroupHilbert G),
        v j • (lp.single 2 (e j) (1 : ℂ) : GroupHilbert G)⟫_ℂ
      = if i = j then star (u i) * v j else 0 := by
    intro j
    rw [inner_smul_left, inner_smul_right, inner_single_single]
    by_cases h : i = j
    · subst h
      simp
    · have hne : e i ≠ e j := fun hEq ↦ h (he hEq)
      simp [hne, h]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j]
  simp [RCLike.inner_apply]

/-! ## The compression -/

/-- The compression `a ↦ J⋆ a J` of a bounded operator to `ℂᵏ`. -/
def compressionLM {k : ℕ}
    (J : EuclideanSpace ℂ (Fin k) →L[ℂ] GroupHilbert G) :
    (GroupHilbert G →L[ℂ] GroupHilbert G) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) where
  toFun a := (ContinuousLinearMap.adjoint J).comp (a.comp J)
  map_add' a b := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp
  map_smul' r a := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp

omit [Group G] in
theorem compressionLM_apply {k : ℕ}
    (J : EuclideanSpace ℂ (Fin k) →L[ℂ] GroupHilbert G)
    (a : GroupHilbert G →L[ℂ] GroupHilbert G) (v : EuclideanSpace ℂ (Fin k)) :
    compressionLM J a v = ContinuousLinearMap.adjoint J (a (J v)) :=
  rfl

/-- The matrix entries of a compression are the matrix coefficients of the
operator against the image of the standard basis. -/
omit [Group G] in
theorem euclideanEntry_compressionLM {k : ℕ}
    (J : EuclideanSpace ℂ (Fin k) →L[ℂ] GroupHilbert G)
    (a : GroupHilbert G →L[ℂ] GroupHilbert G) (p q : Fin k) :
    euclideanEntryLM k p q (compressionLM J a)
      = ⟪J (EuclideanSpace.single p (1 : ℂ)),
          a (J (EuclideanSpace.single q (1 : ℂ)))⟫_ℂ := by
  rw [euclideanEntryLM_apply, compressionLM_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- The compression preserves the adjoint. -/
omit [Group G] in
theorem compressionLM_star {k : ℕ}
    (J : EuclideanSpace ℂ (Fin k) →L[ℂ] GroupHilbert G)
    (a : GroupHilbert G →L[ℂ] GroupHilbert G) :
    compressionLM J (star a) = star (compressionLM J a) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  refine ext_inner_left ℂ fun w ↦ ?_
  have hleft : ⟪w, compressionLM J (star a) v⟫_ℂ
      = ⟪a (J w), J v⟫_ℂ := by
    rw [compressionLM_apply, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have hright : ⟪w, star (compressionLM J a) v⟫_ℂ
      = ⟪a (J w), J v⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, compressionLM_apply,
      ContinuousLinearMap.adjoint_inner_left]
  rw [hleft, hright]

/-- **The compression is completely positive.** -/
theorem isCompletelyPositive_compressionLM {k : ℕ}
    (J : EuclideanSpace ℂ (Fin k) →L[ℂ] GroupHilbert G) :
    IsCompletelyPositive (compressionLM J) := by
  intro n M hM
  obtain ⟨N, hN⟩ := hM
  have hMsa : star M = M := by rw [hN, star_mul, star_star]
  refine exists_factor_of_blockOp_form_nonneg ?_ ?_
  · funext i j
    have hij : star (M j i) = M i j := congrFun (congrFun hMsa i) j
    show star (compressionLM J (M j i)) = compressionLM J (M i j)
    rw [← hij, compressionLM_star]
  · intro v
    rw [inner_blockOp]
    have hterm : ∀ i j : Fin n,
        ⟪v i, (M.map ⇑(compressionLM J)) i j (v j)⟫_ℂ
          = ⟪J (v i), M i j (J (v j))⟫_ℂ := by
      intro i j
      show ⟪v i, compressionLM J (M i j) (v j)⟫_ℂ = _
      rw [compressionLM_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ hterm i j, hN,
      sum_inner_star_mul_self N (fun i ↦ J (v i))]
    have hcast : (∑ r : Fin n,
          ((‖∑ j, N r j (J (v j))‖ : ℝ) : ℂ) ^ 2)
        = (((∑ r : Fin n, ‖∑ j, N r j (J (v j))‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.ofReal_re]
    exact Finset.sum_nonneg fun r _ ↦ sq_nonneg _

/-- The compression along an isometry is unital. -/
theorem compressionLM_one {k : ℕ} {e : Fin k → G} (he : Function.Injective e) :
    compressionLM (folnerIncl e) 1 = 1 := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  refine ext_inner_left ℂ fun w ↦ ?_
  rw [compressionLM_apply, ContinuousLinearMap.adjoint_inner_right]
  show ⟪folnerIncl e w, folnerIncl e v⟫_ℂ = ⟪w, (1 : EuclideanSpace ℂ (Fin k) →L[ℂ]
    EuclideanSpace ℂ (Fin k)) v⟫_ℂ
  rw [inner_folnerIncl he]
  rfl

/-! ## The Følner map back -/

/-- The tuple whose Choi map is the Følner map: `b_p = c_p · λ_{e p}⋆`. -/
def folnerTuple {k : ℕ} (e : Fin k → G) (c : Fin k → ℂ) :
    Fin k → (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  fun p ↦ c p • star (leftRegularOperator G (e p))

/-- **The Følner map** `B(ℂᵏ) → B(ℓ²(G))`,
`T ↦ ∑_{p,q} T_{pq} · c̄_p c_q · λ_{e p} λ_{e q}⋆`. -/
def folnerUp {k : ℕ} (e : Fin k → G) (c : Fin k → ℂ) :
    (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) →ₗ[ℂ]
      (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  choiMap (folnerTuple e c)

theorem folnerUp_apply {k : ℕ} (e : Fin k → G) (c : Fin k → ℂ)
    (T : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :
    folnerUp e c T
      = ∑ p : Fin k, ∑ q : Fin k,
          euclideanEntryLM k p q T
            • (star (folnerTuple e c p) * folnerTuple e c q) :=
  rfl

/-- The generating products of the Følner map are translations. -/
theorem star_folnerTuple_mul_folnerTuple {k : ℕ} (e : Fin k → G)
    (c : Fin k → ℂ) (p q : Fin k) :
    star (folnerTuple e c p) * folnerTuple e c q
      = (star (c p) * c q) • leftRegularOperator G (e p * (e q)⁻¹) := by
  rw [folnerTuple, folnerTuple, star_smul, star_star, smul_mul_assoc,
    mul_smul_comm, smul_smul, star_leftRegularOperator,
    leftRegularOperator_mul]

/-- **The Følner map is completely positive.** -/
theorem isCompletelyPositive_folnerUp {k : ℕ} (e : Fin k → G)
    (c : Fin k → ℂ) :
    IsCompletelyPositive (folnerUp e c) :=
  isCompletelyPositive_choiMap _

/-- The Følner map lands in the reduced algebra. -/
theorem folnerUp_mem_reduced {k : ℕ} (e : Fin k → G) (c : Fin k → ℂ)
    (T : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :
    folnerUp e c T ∈ reducedGroupCStarSubalgebra G := by
  rw [folnerUp_apply]
  refine sum_mem fun p _ ↦ sum_mem fun q _ ↦ ?_
  rw [star_folnerTuple_mul_folnerTuple, smul_smul]
  exact (reducedGroupCStarSubalgebra G).toSubalgebra.smul_mem
    (leftRegularOperator_mem_reduced G (e p * (e q)⁻¹)) _

end

end CStarExactness
end GroupApproximation
