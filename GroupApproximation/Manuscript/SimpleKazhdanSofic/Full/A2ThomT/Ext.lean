import GroupApproximation.Kazhdan.HilbertConvexFixedPoint
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Relative property (T) and the extension lemma (table row A2, Thom's group)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): "Thom constructed a
finitely generated Kazhdan group ...". Thom's proof that `G_0(F_p[t,t⁻¹])` has property (T)
(A. Thom, Groups Geom. Dyn. 4 (2010), §2.1, Lemma 2.1) combines property (T) of the quotient
`SL_3(F_p[t,t⁻¹])` with relative property (T) of the unipotent normal subgroup. This file proves
the abstract ingredients, in the repository's Kazhdan-pair form (`IsKazhdanPair`).

* `IsRelativeKazhdanPair G H Q ε`: every orthogonal representation with a `(Q,ε)`-almost invariant
  unit vector has a nonzero `H`-invariant vector; `HasRelativePropertyT G H`.
* `IsRelativeKazhdanPair.mul_norm_movingProjection_le`: for normal `H`, the component orthogonal to
  the `H`-fixed vectors is controlled by the displacement on `Q`.
* `IsRelativeKazhdanPair.mul_norm_displacement_le`: uniform displacement bound on all of `H`;
  `IsRelativeKazhdanPair.mul_norm_displacement_le_of_hom`: the same pulled along a homomorphism.
* `isRelativeKazhdanPair_of_displacement`: uniform displacement on `H` gives a relative pair.
* `hasKazhdanPropertyT_of_relative`: **extension lemma**: relative (T) for `(G,N)` with `N` normal
  and property (T) for `G ⧸ N` give property (T) for `G`;
  `hasKazhdanPropertyT_of_relative_of_surjective`: the same with a surjection onto a Kazhdan group.
-/

namespace GroupApproximation.Full.A2ThomT

open GroupApproximation GroupApproximation.KazhdanFixedSpace

universe u u' v

/-- A relative Kazhdan pair for a subgroup `H ≤ G`: every orthogonal representation with a
`(Q,ε)`-almost invariant unit vector has a nonzero `H`-invariant vector. -/
def IsRelativeKazhdanPair (G : Type u) [Group G] (H : Subgroup G) (Q : Finset G) (ε : ℝ) :
    Prop :=
  0 < ε ∧
    ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), ∀ x : E, ‖x‖ = 1 →
        (∀ q ∈ Q, ‖ρ q x - x‖ < ε) → ∃ y : E, y ≠ 0 ∧ ∀ h ∈ H, ρ h y = y

/-- Relative property (T) for a pair `(G, H)`, in Kazhdan-pair form. -/
def HasRelativePropertyT (G : Type u) [Group G] (H : Subgroup G) : Prop :=
  ∃ Q : Finset G, ∃ ε : ℝ, IsRelativeKazhdanPair.{u, v} G H Q ε

/-- A Kazhdan pair is a relative Kazhdan pair for every subgroup. -/
theorem IsKazhdanPair.isRelativeKazhdanPair {G : Type u} [Group G] {Q : Finset G} {ε : ℝ}
    (hQ : IsKazhdanPair.{u, v} G Q ε) (H : Subgroup G) :
    IsRelativeKazhdanPair.{u, v} G H Q ε := by
  refine ⟨hQ.1, ?_⟩
  intro E _ _ _ ρ x hx hnear
  obtain ⟨y, hy0, hy⟩ := hQ.2 E ρ x hx hnear
  exact ⟨y, hy0, fun h _ ↦ hy h⟩

section Normal

variable {G : Type u} [Group G] {H : Subgroup G} {Q : Finset G} {ε : ℝ}

/-- For a normal subgroup `H`, a relative Kazhdan pair controls the component of a vector
orthogonal to the `H`-fixed vectors by its displacement on `Q`. -/
theorem IsRelativeKazhdanPair.mul_norm_movingProjection_le [H.Normal]
    (hQ : IsRelativeKazhdanPair.{u, v} G H Q ε)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ q ∈ Q, ‖ρ q x - x‖ ≤ δ) :
    ε * ‖subgroupMovingProjection ρ H x‖ ≤ δ := by
  by_contra hcon
  have hlt : δ < ε * ‖subgroupMovingProjection ρ H x‖ := lt_of_not_ge hcon
  let z : E := subgroupMovingProjection ρ H x
  have hzpos : 0 < ‖z‖ := by
    by_contra hz
    have hz0 : ‖z‖ ≤ 0 := le_of_not_gt hz
    have hprod : ε * ‖z‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hQ.1.le hz0
    have hlt' : δ < ε * ‖z‖ := hlt
    linarith
  let M : Submodule ℝ E := (fixedSubspace ρ H)ᗮ
  letI : CompleteSpace M := (Submodule.isClosed_orthogonal _).completeSpace_coe
  let τ : G →* (M ≃ₗᵢ[ℝ] M) :=
    restrictToInvariantSubspace ρ M fun g w hw ↦
      map_mem_fixedSubspace_orthogonal_of_normal ρ H g hw
  have hzM : z ∈ M := subgroupMovingProjection_mem ρ H x
  let zM : M := ⟨z, hzM⟩
  let u : M := (‖z‖⁻¹ : ℝ) • zM
  have hinvpos : 0 < ‖z‖⁻¹ := inv_pos.mpr hzpos
  have hu : ‖u‖ = 1 := by
    show ‖(‖z‖⁻¹ : ℝ) • zM‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinvpos]
    exact inv_mul_cancel₀ hzpos.ne'
  have hnormal : ∀ g : G, g ∈ Subgroup.normalizer (H : Set G) := by
    intro g
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hnearU : ∀ q ∈ Q, ‖τ q u - u‖ < ε := by
    intro q hq
    have hcoe : ((τ q u - u : M) : E) = (‖z‖⁻¹ : ℝ) • (ρ q z - z) := by
      show ρ q ((‖z‖⁻¹ : ℝ) • z) - (‖z‖⁻¹ : ℝ) • z = (‖z‖⁻¹ : ℝ) • (ρ q z - z)
      rw [map_smul, smul_sub]
    have hdisp : ‖ρ q z - z‖ ≤ δ :=
      (norm_subgroupMovingProjection_displacement_le_of_mem_normalizer ρ H (hnormal q) x).trans
        (hnear q hq)
    have hstep : ‖z‖⁻¹ * δ < ‖z‖⁻¹ * (ε * ‖z‖) := mul_lt_mul_of_pos_left hlt hinvpos
    have hcancel : ‖z‖⁻¹ * (ε * ‖z‖) = ε := by
      rw [mul_comm ε, ← mul_assoc, inv_mul_cancel₀ hzpos.ne', one_mul]
    calc ‖τ q u - u‖ = ‖((τ q u - u : M) : E)‖ := rfl
      _ = ‖z‖⁻¹ * ‖ρ q z - z‖ := by
          rw [hcoe, norm_smul, Real.norm_eq_abs, abs_of_pos hinvpos]
      _ ≤ ‖z‖⁻¹ * δ := mul_le_mul_of_nonneg_left hdisp hinvpos.le
      _ < ‖z‖⁻¹ * (ε * ‖z‖) := hstep
      _ = ε := hcancel
  obtain ⟨y, hy0, hyfix⟩ := hQ.2 M τ u hu hnearU
  have hyF : (y : E) ∈ fixedSubspace ρ H := by
    rw [mem_fixedSubspace_iff]
    intro h hh
    have hval : ((τ h y : M) : E) = (y : E) := congrArg Subtype.val (hyfix h hh)
    exact hval
  have hinner : inner ℝ (y : E) (y : E) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hyF y.2
  exact hy0 (Submodule.coe_eq_zero.mp (inner_self_eq_zero.mp hinner))

/-- For a normal subgroup `H`, a relative Kazhdan pair bounds the displacement of every element of
`H` uniformly by the displacement on `Q`. -/
theorem IsRelativeKazhdanPair.mul_norm_displacement_le [H.Normal]
    (hQ : IsRelativeKazhdanPair.{u, v} G H Q ε)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ q ∈ Q, ‖ρ q x - x‖ ≤ δ) {h : G} (hh : h ∈ H) :
    ε * ‖ρ h x - x‖ ≤ 2 * δ := by
  have h1 := norm_displacement_le_two_mul_norm_subgroupMovingProjection_of_mem ρ H hh x
  have h2 := hQ.mul_norm_movingProjection_le ρ x hδ hnear
  calc ε * ‖ρ h x - x‖ ≤ ε * (2 * ‖subgroupMovingProjection ρ H x‖) :=
        mul_le_mul_of_nonneg_left h1 hQ.1.le
    _ = 2 * (ε * ‖subgroupMovingProjection ρ H x‖) := by ring
    _ ≤ 2 * δ := by linarith

end Normal

/-- The uniform displacement bound, pulled back along a homomorphism `f : P →* G`. -/
theorem IsRelativeKazhdanPair.mul_norm_displacement_le_of_hom {P : Type u'} [Group P]
    {G : Type u} [Group G] {K : Subgroup P} [K.Normal] {Q : Finset P} {ε : ℝ}
    (hQ : IsRelativeKazhdanPair.{u', v} P K Q ε) (f : P →* G)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ q ∈ Q, ‖ρ (f q) x - x‖ ≤ δ) {k : P} (hk : k ∈ K) :
    ε * ‖ρ (f k) x - x‖ ≤ 2 * δ :=
  hQ.mul_norm_displacement_le (ρ.comp f) x hδ hnear hk

/-- A uniform displacement bound on `H` for `(Q,ε)`-almost invariant unit vectors gives a relative
Kazhdan pair: the closed convex hull of the `H`-orbit contains a nonzero fixed vector. -/
theorem isRelativeKazhdanPair_of_displacement {G : Type u} [Group G] (H : Subgroup G)
    (Q : Finset G) {ε : ℝ} (hε : 0 < ε)
    (hdisp : ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), ∀ x : E, ‖x‖ = 1 → (∀ q ∈ Q, ‖ρ q x - x‖ < ε) →
        ∀ h ∈ H, ‖ρ h x - x‖ ≤ 1 / 2) :
    IsRelativeKazhdanPair.{u, v} G H Q ε := by
  refine ⟨hε, ?_⟩
  intro E _ _ _ ρ x hx hnear
  have hbound : ∀ h : H, ‖ρ h.1 x - x‖ ≤ 1 / 2 := fun h ↦ hdisp E ρ x hx hnear h.1 h.2
  obtain ⟨y, hyfix, hyx⟩ := HilbertConvexFixedPoint.exists_fixed_of_orbit_displacement_le
    ρ H x hbound
  refine ⟨y, ?_, fun h hh ↦ hyfix ⟨h, hh⟩⟩
  intro hy0
  rw [hy0, zero_sub, norm_neg, hx] at hyx
  linarith

/-- **Extension lemma** (Thom, GGD 4 (2010), §2.1, proof of Lemma 2.1): if `N` is a normal subgroup
of `G`, the pair `(G,N)` has relative property (T), and `G ⧸ N` has property (T), then `G` has
property (T). -/
theorem hasKazhdanPropertyT_of_relative {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    (hrel : HasRelativePropertyT.{u, v} G N) (hQ : HasKazhdanPropertyT.{u, v} (G ⧸ N)) :
    HasKazhdanPropertyT.{u, v} G := by
  classical
  obtain ⟨S, εN, hpairN⟩ := hrel
  obtain ⟨SQ, εQ, -, hεQ, -, hpairQ⟩ := hQ.exists_identity_pair
  have hεN : 0 < εN := hpairN.1
  let lift : G ⧸ N → G := fun q ↦ (QuotientGroup.mk'_surjective N q).choose
  have hlift : ∀ q : G ⧸ N, ((lift q : G) : G ⧸ N) = q :=
    fun q ↦ (QuotientGroup.mk'_surjective N q).choose_spec
  let ε : ℝ := min (εN / 4) (εQ / 2)
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hεN4 : ε ≤ εN / 4 := min_le_left _ _
  have hεQ2 : ε ≤ εQ / 2 := min_le_right _ _
  refine ⟨S ∪ SQ.image lift, ε, hεpos, ?_⟩
  intro E _ _ _ ρ x hx hnear
  have hnearS : ∀ s ∈ S, ‖ρ s x - x‖ ≤ ε :=
    fun s hs ↦ (hnear s (Finset.mem_union_left _ hs)).le
  have hnearQ : ∀ q ∈ SQ, ‖ρ (lift q) x - x‖ < ε :=
    fun q hq ↦ hnear _ (Finset.mem_union_right _ (Finset.mem_image_of_mem lift hq))
  -- The component orthogonal to the `N`-fixed vectors is small.
  have hmove := hpairN.mul_norm_movingProjection_le ρ x hεpos.le hnearS
  have hZ : ‖subgroupMovingProjection ρ N x‖ ≤ 1 / 4 := by
    have hle : εN * ‖subgroupMovingProjection ρ N x‖ ≤ εN * (1 / 4) := by linarith
    exact le_of_mul_le_mul_left hle hεN
  have hsplit := norm_sq_fixedProjection_add_movingProjection ρ N x
  rw [hx] at hsplit
  have hZsq := mul_self_le_mul_self (norm_nonneg _) hZ
  have hyhalf : 1 / 2 < ‖(fixedProjection ρ N x : E)‖ := by
    nlinarith [norm_nonneg (fixedProjection ρ N x : E)]
  have hPle : ∀ w : E, ‖(fixedProjection ρ N w : E)‖ ≤ ‖w‖ := by
    intro w
    have hw := norm_sq_fixedProjection_add_movingProjection ρ N w
    have hsq : ‖(fixedProjection ρ N w : E)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      nlinarith [sq_nonneg ‖subgroupMovingProjection ρ N w‖]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  -- `G ⧸ N` acts on the `N`-fixed vectors.
  let F : Submodule ℝ E := fixedSubspace ρ N
  letI : CompleteSpace F := (isClosed_fixedSubspace ρ N).completeSpace_coe
  let τ : G →* (F ≃ₗᵢ[ℝ] F) :=
    restrictToInvariantSubspace ρ F fun g w hw ↦ map_mem_fixedSubspace_of_normal ρ N g hw
  have hker : N ≤ τ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply LinearIsometryEquiv.ext
    intro w
    apply Subtype.ext
    show ρ n (w : E) = (w : E)
    exact (mem_fixedSubspace_iff ρ N (w : E)).mp w.2 n hn
  let σ : G ⧸ N →* (F ≃ₗᵢ[ℝ] F) := QuotientGroup.lift N τ hker
  have hσ : ∀ g : G, σ (g : G ⧸ N) = τ g := fun g ↦ QuotientGroup.lift_mk hker g
  let yU : F := fixedProjection ρ N x
  have hyhalf' : 1 / 2 < ‖yU‖ := hyhalf
  have hypos : 0 < ‖yU‖ := lt_trans (by norm_num) hyhalf'
  have hinvpos : 0 < ‖yU‖⁻¹ := inv_pos.mpr hypos
  let u : F := (‖yU‖⁻¹ : ℝ) • yU
  have hu : ‖u‖ = 1 := by
    show ‖(‖yU‖⁻¹ : ℝ) • yU‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinvpos]
    exact inv_mul_cancel₀ hypos.ne'
  have hnearU : ∀ q ∈ SQ, ‖σ q u - u‖ < εQ := by
    intro q hq
    have hq' : σ q = τ (lift q) := by
      rw [← hσ (lift q), hlift q]
    have hcoe : ((τ (lift q) yU - yU : F) : E) =
        (fixedProjection ρ N (ρ (lift q) x - x) : E) := by
      show ρ (lift q) (fixedProjection ρ N x : E) - (fixedProjection ρ N x : E) = _
      rw [map_sub, Submodule.coe_sub, fixedProjection_equivariant_of_normal ρ N (lift q) x]
    have hdispY : ‖τ (lift q) yU - yU‖ < εQ / 2 := by
      calc ‖τ (lift q) yU - yU‖ = ‖((τ (lift q) yU - yU : F) : E)‖ := rfl
        _ = ‖(fixedProjection ρ N (ρ (lift q) x - x) : E)‖ := by rw [hcoe]
        _ ≤ ‖ρ (lift q) x - x‖ := hPle _
        _ < ε := hnearQ q hq
        _ ≤ εQ / 2 := hεQ2
    have hrw : σ q u - u = (‖yU‖⁻¹ : ℝ) • (τ (lift q) yU - yU) := by
      rw [hq']
      show τ (lift q) ((‖yU‖⁻¹ : ℝ) • yU) - (‖yU‖⁻¹ : ℝ) • yU = _
      rw [map_smul, smul_sub]
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos hinvpos]
    have hinvle : ‖yU‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hypos (by norm_num)]
      linarith
    calc ‖yU‖⁻¹ * ‖τ (lift q) yU - yU‖ ≤ 2 * ‖τ (lift q) yU - yU‖ :=
          mul_le_mul_of_nonneg_right hinvle (norm_nonneg _)
      _ < εQ := by linarith
  -- Property (T) for `G ⧸ N` produces the invariant vector.
  obtain ⟨w, hw0, hwfix⟩ := hpairQ.2 F σ u hu hnearU
  refine ⟨(w : E), fun hc ↦ hw0 (Submodule.coe_eq_zero.mp hc), fun g ↦ ?_⟩
  have hg : τ g w = w := by
    rw [← hσ g]
    exact hwfix (g : G ⧸ N)
  exact congrArg Subtype.val hg

/-- **Extension lemma**, surjective form: if `π : G →* Q` is surjective, `(G, ker π)` has relative
property (T) and `Q` has property (T), then `G` has property (T). -/
theorem hasKazhdanPropertyT_of_relative_of_surjective {G : Type u} [Group G] {Q : Type u'}
    [Group Q] (π : G →* Q) (hπ : Function.Surjective π)
    (hrel : HasRelativePropertyT.{u, v} G π.ker) (hQ : HasKazhdanPropertyT.{u', v} Q) :
    HasKazhdanPropertyT.{u, v} G :=
  hasKazhdanPropertyT_of_relative π.ker hrel
    (HasKazhdanPropertyT.of_surjective
      (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.surjective hQ)

end GroupApproximation.Full.A2ThomT
