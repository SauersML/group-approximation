import GroupApproximation.Kazhdan.KazhdanFixedSpace
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Property `(T)` for semidirect products

If `N` and `Q` both have property `(T)`, then so does `SemidirectProduct N Q φ`.

Fix Kazhdan pairs `(S_N, ε_N)` for `N` and `(S_Q, ε_Q)` for `Q`, and control the
semidirect product by the images of `S_N` and `S_Q` with tolerance
`ε_N ε_Q / 4`.  Let `H` be the normal copy of `N`.  On the orthogonal
complement of the fixed space `V^H` the copy of `N` has no invariant vectors, so
an almost invariant unit vector has a small component there and its projection
to `V^H` has norm above `1/2`.  Because `H` is normal, `V^H` is invariant under
the whole group and the projection commutes with the action; `Q` acts on `V^H`
through `inr`, and the normalized projection is almost invariant under `S_Q`.
Property `(T)` for `Q` then gives a nonzero vector of `V^H` fixed by `Q`.  It is
fixed by `H` as well, hence by every `inl n * inr q`, which is every element.
-/

namespace GroupApproximation

universe u v

open KazhdanFixedSpace

namespace SemidirectProductKazhdan

/-- The normal copy of `N` inside `SemidirectProduct N Q φ`, as the kernel of
the projection to `Q`. -/
abbrev normalCopy {N Q : Type u} [Group N] [Group Q] (φ : Q →* MulAut N) :
    Subgroup (SemidirectProduct N Q φ) :=
  (SemidirectProduct.rightHom : SemidirectProduct N Q φ →* Q).ker

theorem inl_mem_normalCopy {N Q : Type u} [Group N] [Group Q]
    {φ : Q →* MulAut N} (n : N) :
    (SemidirectProduct.inl n : SemidirectProduct N Q φ) ∈ normalCopy φ := by
  rw [MonoidHom.mem_ker]
  exact SemidirectProduct.rightHom_inl n

theorem inl_left_eq_of_mem_normalCopy {N Q : Type u} [Group N] [Group Q]
    {φ : Q →* MulAut N} {g : SemidirectProduct N Q φ}
    (hg : g ∈ normalCopy φ) :
    (SemidirectProduct.inl g.left : SemidirectProduct N Q φ) = g := by
  have hr : g.right = 1 := by
    have h := MonoidHom.mem_ker.mp hg
    simpa using h
  calc (SemidirectProduct.inl g.left : SemidirectProduct N Q φ)
      = SemidirectProduct.inl g.left * SemidirectProduct.inr g.right := by
        rw [hr, map_one, mul_one]
    _ = g := SemidirectProduct.inl_left_mul_inr_right g

/-- Displacement by the image of a Kazhdan set of `N` controls the component
orthogonal to the fixed space of the normal copy of `N`. -/
theorem norm_movingProjection_le {N Q : Type u} [Group N] [Group Q]
    {φ : Q →* MulAut N} {S : Finset N} {ε δ : ℝ}
    (hpair : IsKazhdanPair.{u, v} N S ε)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ρ : SemidirectProduct N Q φ →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hnear : ∀ n ∈ S, ‖ρ (SemidirectProduct.inl n) x - x‖ < δ) (hδ : 0 ≤ δ) :
    ε * ‖subgroupMovingProjection ρ (normalCopy φ) x‖ ≤ δ := by
  classical
  by_cases hz0 : subgroupMovingProjection ρ (normalCopy φ) x = 0
  · rw [hz0, norm_zero, mul_zero]
    exact hδ
  · letI : CompleteSpace (subgroupMovingSubspace ρ (normalCopy φ)) :=
      (Submodule.isClosed_orthogonal _).completeSpace_coe
    let τ : N →* (subgroupMovingSubspace ρ (normalCopy φ) ≃ₗᵢ[ℝ]
        subgroupMovingSubspace ρ (normalCopy φ)) :=
      restrictToInvariantSubspace (ρ.comp SemidirectProduct.inl)
        (subgroupMovingSubspace ρ (normalCopy φ)) fun n w hw ↦ by
          exact map_mem_fixedSubspace_orthogonal_of_normal ρ (normalCopy φ)
            (SemidirectProduct.inl n) hw
    have hno : IsKazhdanPair.HasNoInvariantVectors N τ := by
      intro w hw
      have hwfix : (w : E) ∈ fixedSubspace ρ (normalCopy φ) := by
        rw [mem_fixedSubspace_iff]
        intro h hh
        have hval : ρ (SemidirectProduct.inl h.left) (w : E) = w := by
          simpa [τ] using congrArg Subtype.val (hw h.left)
        rwa [inl_left_eq_of_mem_normalCopy hh] at hval
      have hworth : (w : E) ∈ (fixedSubspace ρ (normalCopy φ))ᗮ := w.2
      have hinner : inner ℝ (w : E) w = 0 :=
        Submodule.inner_right_of_mem_orthogonal hwfix hworth
      exact Subtype.ext (inner_self_eq_zero.mp hinner)
    let z : subgroupMovingSubspace ρ (normalCopy φ) :=
      ⟨subgroupMovingProjection ρ (normalCopy φ) x,
        subgroupMovingProjection_mem ρ (normalCopy φ) x⟩
    have hz : z ≠ 0 := fun hc ↦ hz0 (congrArg Subtype.val hc)
    obtain ⟨n, hn, hmove⟩ := hpair.exists_moved_mul_norm_of_noInvariant τ hno z hz
    have hcoe : ((τ n z - z : subgroupMovingSubspace ρ (normalCopy φ)) : E) =
        subgroupMovingProjection ρ (normalCopy φ)
          (ρ (SemidirectProduct.inl n) x - x) := by
      show ρ (SemidirectProduct.inl n) (subgroupMovingProjection ρ (normalCopy φ) x) -
          subgroupMovingProjection ρ (normalCopy φ) x = _
      rw [map_sub, subgroupMovingProjection_equivariant_of_mem ρ (normalCopy φ)
        (inl_mem_normalCopy n) x]
    have hle : ‖τ n z - z‖ ≤ ‖ρ (SemidirectProduct.inl n) x - x‖ := by
      change ‖((τ n z - z : subgroupMovingSubspace ρ (normalCopy φ)) : E)‖ ≤ _
      rw [hcoe]
      exact norm_subgroupMovingProjection_le ρ (normalCopy φ) _
    calc ε * ‖subgroupMovingProjection ρ (normalCopy φ) x‖ = ε * ‖z‖ := rfl
      _ ≤ ‖τ n z - z‖ := hmove
      _ ≤ ‖ρ (SemidirectProduct.inl n) x - x‖ := hle
      _ ≤ δ := (hnear n hn).le

end SemidirectProductKazhdan

open SemidirectProductKazhdan in
/-- **Property `(T)` for semidirect products.**  If `N` and `Q` have property
`(T)`, then so does `SemidirectProduct N Q φ`, for every action `φ`. -/
theorem HasKazhdanPropertyT.semidirectProduct {N Q : Type u} [Group N] [Group Q]
    {φ : Q →* MulAut N} (hN : HasKazhdanPropertyT.{u, v} N)
    (hQ : HasKazhdanPropertyT.{u, v} Q) :
    HasKazhdanPropertyT.{u, v} (SemidirectProduct N Q φ) := by
  classical
  obtain ⟨SN, εN, -, hεN, hεN1, hpairN⟩ := hN.exists_identity_pair
  obtain ⟨SQ, εQ, -, hεQ, hεQ1, hpairQ⟩ := hQ.exists_identity_pair
  have hεpos : 0 < εN * εQ / 4 := div_pos (mul_pos hεN hεQ) (by norm_num)
  refine ⟨SN.image (SemidirectProduct.inl : N →* SemidirectProduct N Q φ) ∪
      SQ.image (SemidirectProduct.inr : Q →* SemidirectProduct N Q φ),
    εN * εQ / 4, hεpos, ?_⟩
  intro E _ _ _ ρ x hx hnear
  have hnearN : ∀ n ∈ SN, ‖ρ (SemidirectProduct.inl n) x - x‖ < εN * εQ / 4 :=
    fun n hn ↦ hnear _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hn))
  have hnearQ : ∀ q ∈ SQ, ‖ρ (SemidirectProduct.inr q) x - x‖ < εN * εQ / 4 :=
    fun q hq ↦ hnear _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))
  -- The component orthogonal to the fixed space of the normal copy is small.
  have hbound := norm_movingProjection_le hpairN ρ x hnearN hεpos.le
  have hZ : ‖subgroupMovingProjection ρ (normalCopy φ) x‖ ≤ 1 / 4 := by
    nlinarith [norm_nonneg (subgroupMovingProjection ρ (normalCopy φ) x)]
  have hsplit := norm_sq_fixedProjection_add_movingProjection ρ (normalCopy φ) x
  rw [hx] at hsplit
  have hZsq := mul_self_le_mul_self (norm_nonneg _) hZ
  have hyhalf : 1 / 2 < ‖(fixedProjection ρ (normalCopy φ) x : E)‖ := by
    nlinarith [norm_nonneg (fixedProjection ρ (normalCopy φ) x : E)]
  have hPle : ∀ v : E, ‖(fixedProjection ρ (normalCopy φ) v : E)‖ ≤ ‖v‖ := by
    intro v
    have hv := norm_sq_fixedProjection_add_movingProjection ρ (normalCopy φ) v
    have hsq : ‖(fixedProjection ρ (normalCopy φ) v : E)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      nlinarith [sq_nonneg ‖subgroupMovingProjection ρ (normalCopy φ) v‖]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  -- `Q` acts on the fixed space of the normal copy.
  letI : CompleteSpace (fixedSubspace ρ (normalCopy φ)) :=
    (isClosed_fixedSubspace ρ (normalCopy φ)).completeSpace_coe
  let σ : Q →* (fixedSubspace ρ (normalCopy φ) ≃ₗᵢ[ℝ]
      fixedSubspace ρ (normalCopy φ)) :=
    restrictToInvariantSubspace (ρ.comp SemidirectProduct.inr)
      (fixedSubspace ρ (normalCopy φ)) fun q w hw ↦ by
        exact map_mem_fixedSubspace_of_normal ρ (normalCopy φ)
          (SemidirectProduct.inr q) hw
  let yU : fixedSubspace ρ (normalCopy φ) := fixedProjection ρ (normalCopy φ) x
  have hyhalf' : 1 / 2 < ‖yU‖ := hyhalf
  have hypos : 0 < ‖yU‖ := lt_trans (by norm_num) hyhalf'
  let u : fixedSubspace ρ (normalCopy φ) := (‖yU‖⁻¹ : ℝ) • yU
  have hu : ‖u‖ = 1 := by
    show ‖(‖yU‖⁻¹ : ℝ) • yU‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hypos),
      inv_mul_cancel₀ hypos.ne']
  have hdispY : ∀ q ∈ SQ, ‖σ q yU - yU‖ < εQ / 4 := by
    intro q hq
    have hcoe : ((σ q yU - yU : fixedSubspace ρ (normalCopy φ)) : E) =
        (fixedProjection ρ (normalCopy φ) (ρ (SemidirectProduct.inr q) x - x) : E) := by
      show ρ (SemidirectProduct.inr q) (fixedProjection ρ (normalCopy φ) x : E) -
          (fixedProjection ρ (normalCopy φ) x : E) = _
      rw [map_sub, Submodule.coe_sub,
        fixedProjection_equivariant_of_normal ρ (normalCopy φ)
          (SemidirectProduct.inr q) x]
    calc ‖σ q yU - yU‖
        = ‖(fixedProjection ρ (normalCopy φ) (ρ (SemidirectProduct.inr q) x - x) : E)‖ := by
          change ‖((σ q yU - yU : fixedSubspace ρ (normalCopy φ)) : E)‖ = _
          rw [hcoe]
      _ ≤ ‖ρ (SemidirectProduct.inr q) x - x‖ := hPle _
      _ < εN * εQ / 4 := hnearQ q hq
      _ ≤ εQ / 4 := by nlinarith
  have hnearU : ∀ q ∈ SQ, ‖σ q u - u‖ < εQ := by
    intro q hq
    have hrw : σ q u - u = (‖yU‖⁻¹ : ℝ) • (σ q yU - yU) := by
      show σ q ((‖yU‖⁻¹ : ℝ) • yU) - (‖yU‖⁻¹ : ℝ) • yU = _
      rw [map_smul, smul_sub]
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hypos)]
    have hinv : ‖yU‖⁻¹ * ‖yU‖ = 1 := inv_mul_cancel₀ hypos.ne'
    have hinvpos : 0 < ‖yU‖⁻¹ := inv_pos.mpr hypos
    have hinvle : ‖yU‖⁻¹ ≤ 2 := by nlinarith
    have hd := hdispY q hq
    calc ‖yU‖⁻¹ * ‖σ q yU - yU‖ ≤ 2 * ‖σ q yU - yU‖ :=
          mul_le_mul_of_nonneg_right hinvle (norm_nonneg _)
      _ < εQ := by linarith
  -- Property `(T)` for `Q` produces the invariant vector.
  obtain ⟨w, hw0, hwfix⟩ := hpairQ.2 (fixedSubspace ρ (normalCopy φ)) σ u hu hnearU
  refine ⟨(w : E), fun hc ↦ hw0 (Submodule.coe_eq_zero.mp hc), fun g ↦ ?_⟩
  have hleft : ρ (SemidirectProduct.inl g.left) (w : E) = w :=
    (mem_fixedSubspace_iff ρ (normalCopy φ) w).mp w.2 _ (inl_mem_normalCopy g.left)
  have hright : ρ (SemidirectProduct.inr g.right) (w : E) = w := by
    simpa [σ] using congrArg Subtype.val (hwfix g.right)
  calc ρ g (w : E)
      = ρ (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right) (w : E) := by
        rw [SemidirectProduct.inl_left_mul_inr_right]
    _ = ρ (SemidirectProduct.inl g.left) (ρ (SemidirectProduct.inr g.right) (w : E)) :=
        congrArg (fun e : E ≃ₗᵢ[ℝ] E ↦ e (w : E)) (map_mul ρ _ _)
    _ = w := by rw [hright, hleft]

end GroupApproximation
