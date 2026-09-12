import GroupApproximation.PropertyT.ThreeVertexProposition
import GroupApproximation.Kazhdan.HilbertConvexFixedPoint
import GroupApproximation.Kazhdan.KazhdanControl

/-!
# The three-subgroup Kazhdan criterion of Ershov--Jaikin-Zapirain

Ershov--Jaikin-Zapirain (*Property (T) for noncommutative universal lattices*, Invent. Math. 179
(2010)), Corollary 3.3(a): let `G = ⟨H₁, H₂, H₃⟩`, with `H₁, H₂` making representation angle at
most `e₃`, `H₁, H₃` at most `e₂` and `H₂, H₃` at most `e₁`, all `< 1`, and suppose
`ε₀ = √2 max{e₁, e₂} / √(1 - e₃) < 1`.  Then `H₁ ∪ H₂ ∪ H₃` is a Kazhdan subset of `G`.

The angle of a pair `H, K` is read in representations of `G` (`MovingAngleLE`): an `H`-fixed and a
`K`-fixed vector, both orthogonal to the `H ⊔ K`-fixed vectors, make angle of cosine at most `e`.
This is the Caprace--Conder--Kaluba--Witzel quantity `ε_{⟨H, K⟩}(H, K)` restricted to the part of a
`G`-representation moved by `⟨H, K⟩`.

The proof is EJZ's: Proposition 3.2 (`ThreeVertexProposition.epsilonOrthogonal_of_projectedAngles`)
bounds the angle between the vertex groups `⟨H₁, H₂⟩` and `⟨H₁, H₃⟩` by `ε₀`, and Lemma 3.1, applied
to that pair and inside each vertex group, turns angles into displacement.  The constant is not
optimized: `κ = (1 - ε₀)(1 - e₂)(1 - e₃) / 4`.
-/

namespace GroupApproximation

universe u v

namespace ThreeVertexKazhdan

open HilbertEpsilonOrthogonality KazhdanFixedSpace

variable {G : Type u} [Group G]

/-- **Representation angle of a pair of subgroups, read in `G`-representations.**  In every
orthogonal representation of `G` on a complete real Hilbert space, an `H`-fixed vector and a
`K`-fixed vector that are both orthogonal to the `H ⊔ K`-fixed vectors make angle of cosine at
most `ε`. -/
def MovingAngleLE (H K : Subgroup G) (epsilon : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E), x ∈ fixedSubspace ρ H → y ∈ fixedSubspace ρ K →
      x ∈ subgroupMovingSubspace ρ (H ⊔ K) → y ∈ subgroupMovingSubspace ρ (H ⊔ K) →
        |inner ℝ x y| ≤ epsilon * ‖x‖ * ‖y‖

/-- The angle hypothesis is symmetric. -/
theorem MovingAngleLE.symm {H K : Subgroup G} {epsilon : ℝ}
    (h : MovingAngleLE.{u, v} H K epsilon) : MovingAngleLE.{u, v} K H epsilon := by
  intro E _ _ _ ρ x y hx hy hxm hym
  rw [sup_comm] at hxm hym
  have hyx := h E ρ y x hy hx hym hxm
  rw [real_inner_comm] at hyx
  linarith [hyx, show epsilon * ‖y‖ * ‖x‖ = epsilon * ‖x‖ * ‖y‖ by ring]

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Fixed subspaces carry orthogonal projections. -/
theorem hasOrthogonalProjection_fixedSubspace (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) :
    (fixedSubspace ρ H).HasOrthogonalProjection := by
  haveI : CompleteSpace (fixedSubspace ρ H) := (isClosed_fixedSubspace ρ H).completeSpace_coe
  infer_instance

/-- A moving angle gives the projected angle of EJZ (3.2): if `H ≤ A`, `K ≤ B` and `L = H ⊔ K`,
the projections to `(V^L)ᗮ` of `V^A` and of `V^B` are `ε`-orthogonal. -/
theorem projectedAngle_of_movingAngle (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {H K L A B : Subgroup G}
    (hL : H ⊔ K = L) (hA : H ≤ A) (hB : K ≤ B) [(fixedSubspace ρ L).HasOrthogonalProjection]
    {epsilon : ℝ} (hmov : MovingAngleLE.{u, v} H K epsilon) :
    ThreeVertexProposition.ProjectedAngle (fixedSubspace ρ A) (fixedSubspace ρ B)
      (fixedSubspace ρ L) epsilon := by
  subst hL
  intro a ha b hb
  have hQa : subgroupMovingProjection ρ (H ⊔ K) a ∈ fixedSubspace ρ H :=
    subgroupMovingProjection_mem_fixedSubspace ρ H (H ⊔ K) le_sup_left
      (KazhdanFixedSpace.antitone ρ hA ha)
  have hQb : subgroupMovingProjection ρ (H ⊔ K) b ∈ fixedSubspace ρ K :=
    subgroupMovingProjection_mem_fixedSubspace ρ K (H ⊔ K) le_sup_right
      (KazhdanFixedSpace.antitone ρ hB hb)
  exact hmov E ρ _ _ hQa hQb (subgroupMovingProjection_mem ρ (H ⊔ K) a)
    (subgroupMovingProjection_mem ρ (H ⊔ K) b)

/-- Uniform displacement below `δ` by `H` bounds the moving part: `‖P_{(V^H)ᗮ} x‖ ≤ δ`. -/
theorem norm_subgroupMovingProjection_le_of_near (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G)
    (x : E) {delta : ℝ} (hnear : ∀ h ∈ H, ‖ρ h x - x‖ < delta) :
    ‖subgroupMovingProjection ρ H x‖ ≤ delta := by
  obtain ⟨y, hy, hyx⟩ :=
    HilbertConvexFixedPoint.exists_near_fixedSubspace ρ H x fun h ↦ (hnear h.1 h.2).le
  have hQy : subgroupMovingProjection ρ H y = 0 := by
    rw [subgroupMovingProjection_eq_sub_fixedProjection]
    let U := fixedSubspace ρ H
    haveI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
    change y - U.starProjection y = 0
    rw [Submodule.starProjection_eq_self_iff.mpr hy, sub_self]
  have hsplit : subgroupMovingProjection ρ H x = subgroupMovingProjection ρ H (x - y) := by
    rw [map_sub, hQy, sub_zero]
  rw [hsplit]
  calc
    ‖subgroupMovingProjection ρ H (x - y)‖ ≤ ‖x - y‖ := norm_subgroupMovingProjection_le ρ H _
    _ = ‖y - x‖ := norm_sub_rev _ _
    _ ≤ delta := hyx

omit [CompleteSpace E] in
/-- The orthogonal projection of `x` to a closed subspace has `⟪P x, x⟫ = ‖P x‖²`. -/
theorem inner_starProjection_self (U : Submodule ℝ E) [U.HasOrthogonalProjection] (x : E) :
    inner ℝ (U.starProjection x) x = ‖U.starProjection x‖ ^ 2 := by
  have h := Submodule.starProjection_inner_eq_zero x (U.starProjection x)
    (U.starProjection_apply_mem x)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
  rw [real_inner_comm]
  linarith

/-- For `q = P_{(V^L)ᗮ} (P_{V^M} z)` fixed by `M`: `⟪q, P_{(V^L)ᗮ} z⟫ = ‖q‖²`. -/
theorem inner_movingProjection_fixedProjection (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (L M : Subgroup G) (z : E)
    (hmem : subgroupMovingProjection ρ L (fixedProjection ρ M z : E) ∈ fixedSubspace ρ M) :
    inner ℝ (subgroupMovingProjection ρ L (fixedProjection ρ M z : E))
        (subgroupMovingProjection ρ L z) =
      ‖subgroupMovingProjection ρ L (fixedProjection ρ M z : E)‖ ^ 2 := by
  haveI : CompleteSpace (fixedSubspace ρ L) := (isClosed_fixedSubspace ρ L).completeSpace_coe
  haveI : CompleteSpace (fixedSubspace ρ M) := (isClosed_fixedSubspace ρ M).completeSpace_coe
  obtain ⟨p, hp⟩ : ∃ p : E, p = (fixedProjection ρ M z : E) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : E, q = subgroupMovingProjection ρ L p := ⟨_, rfl⟩
  rw [← hp, ← hq] at hmem ⊢
  have hqW : q ∈ (fixedSubspace ρ L)ᗮ := by
    rw [hq]
    exact subgroupMovingProjection_mem ρ L p
  have hWq : (fixedSubspace ρ L)ᗮ.starProjection q = q :=
    Submodule.starProjection_eq_self_iff.mpr hqW
  have hWp : (fixedSubspace ρ L)ᗮ.starProjection p = q := by
    rw [hq]
    rfl
  have hMz : (fixedSubspace ρ M).starProjection z = p := by
    rw [hp]
    rfl
  have h2 : inner ℝ q z = inner ℝ q p := by
    have hz := Submodule.starProjection_inner_eq_zero z q hmem
    rw [hMz, inner_sub_left] at hz
    rw [real_inner_comm z q, real_inner_comm p q]
    linarith
  calc
    inner ℝ q (subgroupMovingProjection ρ L z) =
        inner ℝ q ((fixedSubspace ρ L)ᗮ.starProjection z) := rfl
    _ = inner ℝ ((fixedSubspace ρ L)ᗮ.starProjection q) z :=
      (Submodule.inner_starProjection_left_eq_right (fixedSubspace ρ L)ᗮ q z).symm
    _ = inner ℝ q z := by rw [hWq]
    _ = inner ℝ q p := h2
    _ = inner ℝ ((fixedSubspace ρ L)ᗮ.starProjection q) p := by rw [hWq]
    _ = inner ℝ q ((fixedSubspace ρ L)ᗮ.starProjection p) :=
      Submodule.inner_starProjection_left_eq_right (fixedSubspace ρ L)ᗮ q p
    _ = inner ℝ q q := by rw [hWp]
    _ = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q

/-- **EJZ Lemma 3.1 inside a vertex group.**  If `H, K` make moving angle at most `ε ≥ 0`, then
`(1 - ε) ‖P_{(V^{H ⊔ K})ᗮ} x‖² ≤ ‖P_{(V^H)ᗮ} x‖² + ‖P_{(V^K)ᗮ} x‖²`. -/
theorem vertex_moving_sq_le (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H K : Subgroup G) {epsilon : ℝ}
    (heps : 0 ≤ epsilon) (hmov : MovingAngleLE.{u, v} H K epsilon) (x : E) :
    (1 - epsilon) * ‖subgroupMovingProjection ρ (H ⊔ K) x‖ ^ 2 ≤
      ‖subgroupMovingProjection ρ H x‖ ^ 2 + ‖subgroupMovingProjection ρ K x‖ ^ 2 := by
  have haH : subgroupMovingProjection ρ (H ⊔ K) (fixedProjection ρ H x : E) ∈
      fixedSubspace ρ H :=
    subgroupMovingProjection_mem_fixedSubspace ρ H (H ⊔ K) le_sup_left
      (fixedProjection ρ H x).2
  have hbK : subgroupMovingProjection ρ (H ⊔ K) (fixedProjection ρ K x : E) ∈
      fixedSubspace ρ K :=
    subgroupMovingProjection_mem_fixedSubspace ρ K (H ⊔ K) le_sup_right
      (fixedProjection ρ K x).2
  have hab := hmov E ρ _ _ haH hbK (subgroupMovingProjection_mem ρ (H ⊔ K) _)
    (subgroupMovingProjection_mem ρ (H ⊔ K) _)
  have haw := inner_movingProjection_fixedProjection ρ (H ⊔ K) H x haH
  have hbw := inner_movingProjection_fixedProjection ρ (H ⊔ K) K x hbK
  have hmain := ThreeVertexClosure.sq_norm_le_sub_add_sub heps haw hbw hab
  have hwa : ‖subgroupMovingProjection ρ (H ⊔ K) x -
      subgroupMovingProjection ρ (H ⊔ K) (fixedProjection ρ H x : E)‖ ≤
        ‖subgroupMovingProjection ρ H x‖ := by
    rw [← map_sub, subgroupMovingProjection_eq_sub_fixedProjection ρ H x]
    exact norm_subgroupMovingProjection_le ρ (H ⊔ K) _
  have hwb : ‖subgroupMovingProjection ρ (H ⊔ K) x -
      subgroupMovingProjection ρ (H ⊔ K) (fixedProjection ρ K x : E)‖ ≤
        ‖subgroupMovingProjection ρ K x‖ := by
    rw [← map_sub, subgroupMovingProjection_eq_sub_fixedProjection ρ K x]
    exact norm_subgroupMovingProjection_le ρ (H ⊔ K) _
  have hwa2 := pow_le_pow_left₀ (norm_nonneg _) hwa 2
  have hwb2 := pow_le_pow_left₀ (norm_nonneg _) hwb 2
  linarith

/-- **The Kazhdan subset from three moving angles** (EJZ Corollary 3.3(a), constant not
optimized).  Let `H₁ ⊔ H₂ ⊔ H₃ = ⊤`, with moving angles `e₃` for `(H₁, H₂)`, `e₂` for `(H₁, H₃)`
and `e₁` for `(H₂, H₃)`, all in `[0, 1)`, and let `ε₀ ∈ [0, 1)` satisfy
`2 max(e₁, e₂)² ≤ ε₀² (1 - e₃)`.  Then `H₁ ∪ H₂ ∪ H₃` is a Kazhdan subset of `G` with constant
`(1 - ε₀)(1 - e₂)(1 - e₃) / 4`. -/
theorem isKazhdanSubset_of_movingAngles (H₁ H₂ H₃ : Subgroup G) (hgen : H₁ ⊔ H₂ ⊔ H₃ = ⊤)
    {e₁ e₂ e₃ epsilon₀ : ℝ} (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₃ : 0 ≤ e₃)
    (he₁1 : e₁ < 1) (he₂1 : e₂ < 1) (he₃1 : e₃ < 1) (heps₀ : 0 ≤ epsilon₀)
    (heps₀1 : epsilon₀ < 1) (hconst : 2 * max e₁ e₂ ^ 2 ≤ epsilon₀ ^ 2 * (1 - e₃))
    (h₁₂ : MovingAngleLE.{u, v} H₁ H₂ e₃) (h₁₃ : MovingAngleLE.{u, v} H₁ H₃ e₂)
    (h₂₃ : MovingAngleLE.{u, v} H₂ H₃ e₁) :
    IsKazhdanSubset.{u, v} G ((H₁ : Set G) ∪ H₂ ∪ H₃)
      ((1 - epsilon₀) * (1 - e₂) * (1 - e₃) / 4) := by
  have hc0 : 0 < (1 - epsilon₀) * (1 - e₂) * (1 - e₃) :=
    mul_pos (mul_pos (sub_pos.mpr heps₀1) (sub_pos.mpr he₂1)) (sub_pos.mpr he₃1)
  have hc1 : (1 - epsilon₀) * (1 - e₂) * (1 - e₃) ≤ 1 := by
    have h1 : 0 ≤ 1 - epsilon₀ := (sub_pos.mpr heps₀1).le
    have h2 : 0 ≤ 1 - e₂ := (sub_pos.mpr he₂1).le
    have h2' : 1 - e₂ ≤ 1 := by linarith
    have h3' : 1 - e₃ ≤ 1 := by linarith
    have h1' : 1 - epsilon₀ ≤ 1 := by linarith
    have h12 : (1 - epsilon₀) * (1 - e₂) ≤ 1 := by nlinarith
    nlinarith [mul_nonneg h1 h2]
  refine ⟨div_pos hc0 (by norm_num), ?_⟩
  intro E _ _ _ ρ x hx hnear
  by_contra hinv
  have hno : IsKazhdanPair.HasNoInvariantVectors G ρ := by
    intro y hy
    by_contra hy0
    exact hinv ⟨y, hy0, hy⟩
  let κ : ℝ := (1 - epsilon₀) * (1 - e₂) * (1 - e₃) / 4
  have hnear₁ : ∀ h ∈ H₁, ‖ρ h x - x‖ < κ := fun h hh ↦ hnear h (Or.inl (Or.inl hh))
  have hnear₂ : ∀ h ∈ H₂, ‖ρ h x - x‖ < κ := fun h hh ↦ hnear h (Or.inl (Or.inr hh))
  have hnear₃ : ∀ h ∈ H₃, ‖ρ h x - x‖ < κ := fun h hh ↦ hnear h (Or.inr hh)
  have hm₁ := norm_subgroupMovingProjection_le_of_near ρ H₁ x hnear₁
  have hm₂ := norm_subgroupMovingProjection_le_of_near ρ H₂ x hnear₂
  have hm₃ := norm_subgroupMovingProjection_le_of_near ρ H₃ x hnear₃
  have hm₁2 := pow_le_pow_left₀ (norm_nonneg _) hm₁ 2
  have hm₂2 := pow_le_pow_left₀ (norm_nonneg _) hm₂ 2
  have hm₃2 := pow_le_pow_left₀ (norm_nonneg _) hm₃ 2
  -- the two vertex groups
  have hv₃ := vertex_moving_sq_le ρ H₁ H₂ he₃ h₁₂ x
  have hv₂ := vertex_moving_sq_le ρ H₁ H₃ he₂ h₁₃ x
  -- the angle between the vertex groups, EJZ Proposition 3.2
  haveI := hasOrthogonalProjection_fixedSubspace ρ (H₂ ⊔ H₃)
  haveI := hasOrthogonalProjection_fixedSubspace ρ (H₁ ⊔ H₃)
  haveI := hasOrthogonalProjection_fixedSubspace ρ (H₁ ⊔ H₂)
  have hA₃ : ThreeVertexProposition.ProjectedAngle (fixedSubspace ρ (H₁ ⊔ H₃))
      (fixedSubspace ρ (H₂ ⊔ H₃)) (fixedSubspace ρ (H₁ ⊔ H₂)) e₃ :=
    projectedAngle_of_movingAngle ρ rfl le_sup_left le_sup_left h₁₂
  have hA₂ : ThreeVertexProposition.ProjectedAngle (fixedSubspace ρ (H₁ ⊔ H₂))
      (fixedSubspace ρ (H₂ ⊔ H₃)) (fixedSubspace ρ (H₁ ⊔ H₃)) e₂ :=
    projectedAngle_of_movingAngle ρ rfl le_sup_left le_sup_right h₁₃
  have hA₁ : ThreeVertexProposition.ProjectedAngle (fixedSubspace ρ (H₁ ⊔ H₃))
      (fixedSubspace ρ (H₁ ⊔ H₂)) (fixedSubspace ρ (H₂ ⊔ H₃)) e₁ :=
    projectedAngle_of_movingAngle ρ (sup_comm H₃ H₂) le_sup_right le_sup_right h₂₃.symm
  have htop : (H₁ ⊔ H₃) ⊔ (H₁ ⊔ H₂) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_right))
      (le_sup_right.trans le_sup_left)
  have hbot : fixedSubspace ρ (H₁ ⊔ H₃) ⊓ fixedSubspace ρ (H₁ ⊔ H₂) = ⊥ := by
    rw [← fixedSubspace_sup, htop, fixedSubspace_top_eq_bot ρ hno]
  have hV32 := ThreeVertexProposition.epsilonOrthogonal_of_projectedAngles
    (fixedSubspace ρ (H₂ ⊔ H₃)) (fixedSubspace ρ (H₁ ⊔ H₃)) (fixedSubspace ρ (H₁ ⊔ H₂))
    he₁ he₂ he₃ he₁1 he₂1 he₃1 heps₀ heps₀1 hconst hbot hA₃ hA₂ hA₁
  -- EJZ Lemma 3.1 for the pair of vertex groups
  have hpair := ThreeVertexClosure.sq_norm_le_sub_add_sub heps₀
    (inner_starProjection_self (fixedSubspace ρ (H₁ ⊔ H₂)) x)
    (inner_starProjection_self (fixedSubspace ρ (H₁ ⊔ H₃)) x)
    (hV32 _ ((fixedSubspace ρ (H₁ ⊔ H₂)).starProjection_apply_mem x) _
      ((fixedSubspace ρ (H₁ ⊔ H₃)).starProjection_apply_mem x))
  have hs₃ : ‖x - (fixedSubspace ρ (H₁ ⊔ H₂)).starProjection x‖ =
      ‖subgroupMovingProjection ρ (H₁ ⊔ H₂) x‖ :=
    (congrArg norm (subgroupMovingProjection_eq_sub_fixedProjection ρ (H₁ ⊔ H₂) x)).symm
  have hs₂ : ‖x - (fixedSubspace ρ (H₁ ⊔ H₃)).starProjection x‖ =
      ‖subgroupMovingProjection ρ (H₁ ⊔ H₃) x‖ :=
    (congrArg norm (subgroupMovingProjection_eq_sub_fixedProjection ρ (H₁ ⊔ H₃) x)).symm
  rw [hs₃, hs₂, hx] at hpair
  -- numerics
  set s₃ := ‖subgroupMovingProjection ρ (H₁ ⊔ H₂) x‖ ^ 2 with hs₃def
  set s₂ := ‖subgroupMovingProjection ρ (H₁ ⊔ H₃) x‖ ^ 2 with hs₂def
  have hs₃0 : 0 ≤ s₃ := sq_nonneg _
  have hs₂0 : 0 ≤ s₂ := sq_nonneg _
  have hκ0 : 0 ≤ κ := (div_pos hc0 (by norm_num)).le
  have hb₃ : (1 - e₃) * s₃ ≤ 2 * κ ^ 2 := by linarith
  have hb₂ : (1 - e₂) * s₂ ≤ 2 * κ ^ 2 := by linarith
  have hc : (1 - epsilon₀) * (1 - e₂) * (1 - e₃) ≤ 4 * κ ^ 2 := by
    have hsum : (1 - epsilon₀) * 1 ^ 2 ≤ s₃ + s₂ := hpair
    have h2 : 0 ≤ 1 - e₂ := (sub_pos.mpr he₂1).le
    have h3 : 0 ≤ 1 - e₃ := (sub_pos.mpr he₃1).le
    have hstep : (1 - epsilon₀) * (1 - e₂) * (1 - e₃) ≤ (1 - e₂) * (1 - e₃) * (s₃ + s₂) := by
      have := mul_le_mul_of_nonneg_left hsum (mul_nonneg h2 h3)
      nlinarith [this]
    have hA : (1 - e₂) * ((1 - e₃) * s₃) ≤ (1 - e₂) * (2 * κ ^ 2) :=
      mul_le_mul_of_nonneg_left hb₃ h2
    have hB : (1 - e₃) * ((1 - e₂) * s₂) ≤ (1 - e₃) * (2 * κ ^ 2) :=
      mul_le_mul_of_nonneg_left hb₂ h3
    have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
    nlinarith [hstep, hA, hB, hκ2, he₂, he₃]
  have hκdef : 4 * κ = (1 - epsilon₀) * (1 - e₂) * (1 - e₃) := by
    show 4 * ((1 - epsilon₀) * (1 - e₂) * (1 - e₃) / 4) = _
    ring
  have hκle : κ ≤ 1 / 4 := by linarith
  have hκpos : 0 < κ := div_pos hc0 (by norm_num)
  nlinarith [hc, hκdef, hκle, hκpos]

end ThreeVertexKazhdan
end GroupApproximation

#audit_axioms GroupApproximation.ThreeVertexKazhdan.MovingAngleLE.symm
#audit_axioms GroupApproximation.ThreeVertexKazhdan.projectedAngle_of_movingAngle
#audit_axioms GroupApproximation.ThreeVertexKazhdan.norm_subgroupMovingProjection_le_of_near
#audit_axioms GroupApproximation.ThreeVertexKazhdan.inner_movingProjection_fixedProjection
#audit_axioms GroupApproximation.ThreeVertexKazhdan.vertex_moving_sq_le
#audit_axioms GroupApproximation.ThreeVertexKazhdan.isKazhdanSubset_of_movingAngles
