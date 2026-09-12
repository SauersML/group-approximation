import GroupApproximation.Kazhdan.EJZAngleTranslates
import GroupApproximation.Kazhdan.KMSGroupPresentation
import GroupApproximation.PropertyT.ThreeVertexKazhdan

/-!
# The representation angle of the Heisenberg group `U₃(p)`

Caprace--Conder--Kaluba--Witzel (arXiv:2011.09276), Proposition 7.3(i), after Ershov--Jaikin-Zapirain
§4.1: in `U₃(p) = ⟨a, b | aᵖ, bᵖ, [a,b,a], [a,b,b]⟩` the subgroups `⟨a⟩` and `⟨b⟩` make
representation angle `1/√p`.

The proof here uses only the relations `bᵖ = 1`, `zᵖ = 1` and that `z = [a, b] = a⁻¹b⁻¹ab` commutes
with `a` and `b`, so it applies to the vertex subgroup `⟨a, b⟩` of `GHB(p)` directly, in every
orthogonal representation of the ambient group, without identifying the vertex group.

Let `x` be `a`-fixed, `y` be `b`-fixed, both orthogonal to the `⟨a, b⟩`-fixed vectors.  Split both
along the fixed space of `⟨z⟩`.
* On the `z`-fixed parts `u, v`: `∑_j ρ(bʲ) u` is fixed by `a` and `b`, hence orthogonal to `v`,
  and it pairs with `v` as `p ⟪u, v⟫`.  So `⟪u, v⟫ = 0`.
* On the `z`-moving parts `u, v`: `ρ(a) ρ(bᵐ) u = ρ(zᵐ) ρ(bᵐ) u`, so for `0 < m < p` the translate
  `ρ(bᵐ) u` is orthogonal to `u` (`EJZAngleTranslates.inner_eq_zero_of_twisted`).  The translate
  sum has `‖T‖² = p ‖u‖²` and `p² ⟪u, v⟫² ≤ ‖T‖² ‖v‖²`, so `p ⟪u, v⟫² ≤ ‖u‖² ‖v‖²`.
-/

namespace GroupApproximation

universe u v

namespace EJZAngleHeisenberg

open KazhdanFixedSpace EJZAngleTranslates

variable {G : Type u} [Group G]

/-- With `z = [a, b] = a⁻¹b⁻¹ab`: `a b = b a z`. -/
theorem mul_eq_mul_mul_comm (a b : G) : a * b = b * a * KMSGroup.comm a b := by
  simp [KMSGroup.comm, mul_assoc]

/-- If `z = [a, b]` commutes with `a` and `b`, then `a bᵐ = zᵐ bᵐ a`. -/
theorem mul_pow_eq_of_central {a b : G} (hza : Commute (KMSGroup.comm a b) a)
    (hzb : Commute (KMSGroup.comm a b) b) (m : ℕ) :
    a * b ^ m = KMSGroup.comm a b ^ m * b ^ m * a := by
  set z := KMSGroup.comm a b with hz
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      a * b ^ (m + 1) = (a * b ^ m) * b := by rw [pow_succ, mul_assoc]
      _ = (z ^ m * b ^ m * a) * b := by rw [ih]
      _ = z ^ m * b ^ m * (a * b) := by simp only [mul_assoc]
      _ = z ^ m * b ^ m * (b * a * z) := by rw [hz, mul_eq_mul_mul_comm a b]
      _ = z ^ m * (b ^ m * b) * (a * z) := by simp only [mul_assoc]
      _ = z ^ m * b ^ (m + 1) * (z * a) := by rw [← pow_succ, hza.eq]
      _ = z ^ m * (b ^ (m + 1) * z) * a := by simp only [mul_assoc]
      _ = z ^ m * (z * b ^ (m + 1)) * a := by rw [(hzb.pow_right (m + 1)).eq]
      _ = z ^ (m + 1) * b ^ (m + 1) * a := by rw [pow_succ z m]; simp only [mul_assoc]

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For an `a`-fixed vector `x`: `ρ(a) ρ(bᵐ) x = ρ(zᵐ) ρ(bᵐ) x`. -/
theorem apply_translate_of_fixed (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {a b : G}
    (hza : Commute (KMSGroup.comm a b) a) (hzb : Commute (KMSGroup.comm a b) b) (m : ℕ)
    {x : E} (hx : ρ a x = x) :
    ρ a (ρ (b ^ m) x) = ρ (KMSGroup.comm a b ^ m) (ρ (b ^ m) x) := by
  have h := congrArg (fun g ↦ ρ g x) (mul_pow_eq_of_central hza hzb m)
  simp only [map_mul] at h
  change ρ a (ρ (b ^ m) x) = ρ (KMSGroup.comm a b ^ m) (ρ (b ^ m) (ρ a x)) at h
  rw [hx] at h
  exact h

/-- Splitting an inner product along the fixed space of a subgroup. -/
theorem inner_eq_fixed_add_moving [CompleteSpace E] (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G)
    (x y : E) :
    inner ℝ x y = inner ℝ (fixedProjection ρ H x : E) (fixedProjection ρ H y : E) +
      inner ℝ (subgroupMovingProjection ρ H x) (subgroupMovingProjection ρ H y) := by
  rw [subgroupMovingProjection_eq_sub_fixedProjection,
    subgroupMovingProjection_eq_sub_fixedProjection]
  let U : Submodule ℝ E := fixedSubspace ρ H
  haveI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  change inner ℝ x y = inner ℝ (U.starProjection x) (U.starProjection y) +
    inner ℝ (x - U.starProjection x) (y - U.starProjection y)
  have h1 := Submodule.starProjection_inner_eq_zero x (U.starProjection y)
    (U.starProjection_apply_mem y)
  have h2 := Submodule.starProjection_inner_eq_zero y (U.starProjection x)
    (U.starProjection_apply_mem x)
  rw [inner_sub_left] at h1 h2
  simp only [inner_sub_left, inner_sub_right]
  linarith [real_inner_comm (U.starProjection x) y,
    real_inner_comm (U.starProjection x) (U.starProjection y)]

variable [CompleteSpace E]

/-- An element commuting with `z` normalizes `⟨z⟩`. -/
theorem mem_normalizer_zpowers {g z : G} (h : Commute z g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact (h.zpow_left k).eq

/-- A `g`-fixed vector keeps `g`-fixed parts along the fixed space of a subgroup `g` normalizes. -/
theorem projections_fixed {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E} (hx : ρ g x = x) :
    ρ g (fixedProjection ρ H x : E) = fixedProjection ρ H x ∧
      ρ g (subgroupMovingProjection ρ H x) = subgroupMovingProjection ρ H x := by
  constructor
  · rw [← fixedProjection_equivariant_of_mem_normalizer ρ H hg, hx]
  · rw [← subgroupMovingProjection_equivariant_of_mem_normalizer ρ H hg, hx]

omit [CompleteSpace E] in
/-- **The `z`-fixed parts are orthogonal.**  If `u` is fixed by `a` and by `z = [a, b]`, `v` is
`b`-fixed and orthogonal to the `⟨a⟩ ⊔ ⟨b⟩`-fixed vectors, then `⟪u, v⟫ = 0`: the translate sum
`∑_{j<p} ρ(bʲ) u` is fixed by `a` and `b` and pairs with `v` as `p ⟪u, v⟫`. -/
theorem inner_eq_zero_of_center_fixed (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} (hp0 : 0 < p) {a b : G}
    (hb : b ^ p = 1) (hza : Commute (KMSGroup.comm a b) a)
    (hzb : Commute (KMSGroup.comm a b) b) {u w : E} (hua : ρ a u = u)
    (huz : ρ (KMSGroup.comm a b) u = u) (hwb : ρ b w = w)
    (hwL : w ∈ (fixedSubspace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b))ᗮ) :
    inner ℝ u w = 0 := by
  have hTa : ρ a (translateSum ρ b p u) = translateSum ρ b p u := by
    unfold translateSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [apply_translate_of_fixed ρ hza hzb m hua]
    have hc : ρ (KMSGroup.comm a b ^ m) (ρ (b ^ m) u) =
        ρ (b ^ m) (ρ (KMSGroup.comm a b ^ m) u) := by
      have h := congrArg (fun g ↦ ρ g u) (hzb.pow_pow m m).eq
      simp only [map_mul] at h
      exact h
    rw [hc, pow_apply_of_fixed ρ huz m]
  have hTb : ρ b (translateSum ρ b p u) = translateSum ρ b p u := translateSum_fixed ρ hb u
  have hTL : translateSum ρ b p u ∈ fixedSubspace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    rw [fixedSubspace_sup]
    exact ⟨(mem_fixedSubspace_zpowers_iff ρ a _).mpr hTa,
      (mem_fixedSubspace_zpowers_iff ρ b _).mpr hTb⟩
  have hzero : inner ℝ (translateSum ρ b p u) w = 0 :=
    Submodule.inner_right_of_mem_orthogonal hTL hwL
  rw [inner_translateSum_of_fixed ρ b p u hwb] at hzero
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  exact (mul_eq_zero.mp hzero).resolve_left hp'

/-- **The `z`-moving parts obey the `1/√p` bound.**  If `u` is `a`-fixed and orthogonal to the
`⟨z⟩`-fixed vectors and `w` is `b`-fixed, then `p ⟪u, w⟫² ≤ ‖u‖² ‖w‖²`. -/
theorem sq_inner_le_of_center_moving (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} (hp : p.Prime) {a b : G}
    (hb : b ^ p = 1) (hza : Commute (KMSGroup.comm a b) a)
    (hzb : Commute (KMSGroup.comm a b) b) (hz : KMSGroup.comm a b ^ p = 1) {u w : E}
    (hua : ρ a u = u) (huZ : u ∈ (fixedSubspace ρ (Subgroup.zpowers (KMSGroup.comm a b)))ᗮ)
    (hwb : ρ b w = w) :
    (p : ℝ) * inner ℝ u w ^ 2 ≤ ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
  have hp0 : 0 < p := hp.pos
  have hgram : ∀ m ∈ Finset.range p, m ≠ 0 → inner ℝ u (ρ (b ^ m) u) = 0 := by
    intro m hm hm0
    have hmp : m < p := Finset.mem_range.mp hm
    have hcop : Nat.Coprime m p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm0) hmp)).symm
    exact inner_eq_zero_of_twisted ρ hp0 hz hza.symm
      (exists_pow_mul_eq_pow hz hp0.ne' hcop) hua (apply_translate_of_fixed ρ hza hzb m hua) huZ
  have hsum : ∑ m ∈ Finset.range p, inner ℝ u (ρ (b ^ m) u) = ‖u‖ ^ 2 := by
    rw [Finset.sum_eq_single 0 hgram (fun h ↦ absurd (Finset.mem_range.mpr hp0) h)]
    simp [real_inner_self_eq_norm_sq]
  have hT := norm_sq_translateSum ρ hb u
  rw [hsum] at hT
  have hcs := sq_inner_le_of_translateSum ρ b p u hwb
  rw [hT] at hcs
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp0
  have h3 : (p : ℝ) * ((p : ℝ) * inner ℝ u w ^ 2) ≤ (p : ℝ) * (‖u‖ ^ 2 * ‖w‖ ^ 2) := by
    nlinarith [hcs]
  exact le_of_mul_le_mul_left h3 hppos

/-- **The Heisenberg angle.**  Let `z = [a, b]` commute with `a` and `b`, with `bᵖ = zᵖ = 1` and `p`
prime.  If `x` is `a`-fixed, `y` is `b`-fixed and both are orthogonal to the `⟨a⟩ ⊔ ⟨b⟩`-fixed
vectors, then `p ⟪x, y⟫² ≤ ‖x‖² ‖y‖²`. -/
theorem sq_inner_le_heisenberg (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} (hp : p.Prime) {a b : G}
    (hb : b ^ p = 1) (hza : Commute (KMSGroup.comm a b) a)
    (hzb : Commute (KMSGroup.comm a b) b) (hz : KMSGroup.comm a b ^ p = 1) {x y : E}
    (hx : ρ a x = x) (hy : ρ b y = y)
    (hym : y ∈ subgroupMovingSubspace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) :
    (p : ℝ) * inner ℝ x y ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hzL : KMSGroup.comm a b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    have ha : a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    have hb' : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    rw [KMSGroup.comm]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha)
      (Subgroup.inv_mem _ hb')) ha) hb'
  have hZL : Subgroup.zpowers (KMSGroup.comm a b) ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.zpowers_le.mpr hzL
  have hanorm := mem_normalizer_zpowers hza
  have hbnorm := mem_normalizer_zpowers hzb
  obtain ⟨hPxa, hQxa⟩ := projections_fixed hanorm ρ hx
  obtain ⟨hPyb, hQyb⟩ := projections_fixed hbnorm ρ hy
  haveI : CompleteSpace (fixedSubspace ρ (Subgroup.zpowers (KMSGroup.comm a b))) :=
    (isClosed_fixedSubspace ρ _).completeSpace_coe
  have hPxz : ρ (KMSGroup.comm a b) (fixedProjection ρ (Subgroup.zpowers (KMSGroup.comm a b)) x : E) =
      fixedProjection ρ (Subgroup.zpowers (KMSGroup.comm a b)) x :=
    (mem_fixedSubspace_zpowers_iff ρ _ _).mp (fixedProjection ρ _ x).2
  have hPyL : (fixedProjection ρ (Subgroup.zpowers (KMSGroup.comm a b)) y : E) ∈
      (fixedSubspace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro g hg
    have hgZ : (fixedSubspace ρ (Subgroup.zpowers (KMSGroup.comm a b))).starProjection g = g :=
      Submodule.starProjection_eq_self_iff.mpr (KazhdanFixedSpace.antitone ρ hZL hg)
    change inner ℝ g ((fixedSubspace ρ (Subgroup.zpowers (KMSGroup.comm a b))).starProjection y) = 0
    rw [← Submodule.inner_starProjection_left_eq_right, hgZ]
    exact Submodule.inner_right_of_mem_orthogonal hg hym
  have hfixed := inner_eq_zero_of_center_fixed ρ hp.pos hb hza hzb hPxa hPxz hPyb hPyL
  have hmoving := sq_inner_le_of_center_moving ρ hp hb hza hzb hz hQxa
    (subgroupMovingProjection_mem ρ _ x) hQyb
  have hsplit := inner_eq_fixed_add_moving ρ (Subgroup.zpowers (KMSGroup.comm a b)) x y
  rw [hfixed, zero_add] at hsplit
  have hux := norm_subgroupMovingProjection_le ρ (Subgroup.zpowers (KMSGroup.comm a b)) x
  have hvy := norm_subgroupMovingProjection_le ρ (Subgroup.zpowers (KMSGroup.comm a b)) y
  have hux2 := pow_le_pow_left₀ (norm_nonneg _) hux 2
  have hvy2 := pow_le_pow_left₀ (norm_nonneg _) hvy 2
  rw [hsplit]
  exact hmoving.trans (mul_le_mul hux2 hvy2 (sq_nonneg _) (sq_nonneg _))

omit [CompleteSpace E] in
/-- From `p ⟪x, y⟫² ≤ ‖x‖² ‖y‖²` and `1 ≤ p ε²` to `|⟪x, y⟫| ≤ ε ‖x‖ ‖y‖`. -/
theorem abs_inner_le_of_sq {p : ℕ} {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (hpe : 1 ≤ (p : ℝ) * epsilon ^ 2) {x y : E}
    (h : (p : ℝ) * inner ℝ x y ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2) :
    |inner ℝ x y| ≤ epsilon * ‖x‖ * ‖y‖ := by
  have hsq : inner ℝ x y ^ 2 ≤ (epsilon * ‖x‖ * ‖y‖) ^ 2 := by
    have hi : 0 ≤ inner ℝ x y ^ 2 := sq_nonneg _
    have hn : 0 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by positivity
    calc
      inner ℝ x y ^ 2 ≤ ((p : ℝ) * epsilon ^ 2) * inner ℝ x y ^ 2 := by nlinarith
      _ = epsilon ^ 2 * ((p : ℝ) * inner ℝ x y ^ 2) := by ring
      _ ≤ epsilon ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = (epsilon * ‖x‖ * ‖y‖) ^ 2 := by ring
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  exact hsq

end EJZAngleHeisenberg

/-- **Moving angle of a Heisenberg pair** (CCKW Proposition 7.3(i), character-free): if
`z = [a, b]` commutes with `a` and `b`, `bᵖ = zᵖ = 1`, `p` is prime and `1 ≤ p ε²`, then `⟨a⟩` and
`⟨b⟩` make moving angle at most `ε`. -/
theorem EJZAngleHeisenberg.movingAngleLE_heisenberg {G : Type u} [Group G] {p : ℕ} (hp : p.Prime)
    {a b : G} (hb : b ^ p = 1) (hza : Commute (KMSGroup.comm a b) a)
    (hzb : Commute (KMSGroup.comm a b) b) (hz : KMSGroup.comm a b ^ p = 1) {epsilon : ℝ}
    (heps : 0 ≤ epsilon) (hpe : 1 ≤ (p : ℝ) * epsilon ^ 2) :
    ThreeVertexKazhdan.MovingAngleLE.{u, v} (Subgroup.zpowers a) (Subgroup.zpowers b) epsilon := by
  intro E _ _ _ ρ x y hx hy _hxm hym
  have hx' : ρ a x = x := (EJZAngleTranslates.mem_fixedSubspace_zpowers_iff ρ a x).mp hx
  have hy' : ρ b y = y := (EJZAngleTranslates.mem_fixedSubspace_zpowers_iff ρ b y).mp hy
  exact EJZAngleHeisenberg.abs_inner_le_of_sq heps hpe
    (EJZAngleHeisenberg.sq_inner_le_heisenberg ρ hp hb hza hzb hz hx' hy' hym)

end GroupApproximation

#audit_axioms GroupApproximation.EJZAngleHeisenberg.mul_pow_eq_of_central
#audit_axioms GroupApproximation.EJZAngleHeisenberg.apply_translate_of_fixed
#audit_axioms GroupApproximation.EJZAngleHeisenberg.inner_eq_fixed_add_moving
#audit_axioms GroupApproximation.EJZAngleHeisenberg.inner_eq_zero_of_center_fixed
#audit_axioms GroupApproximation.EJZAngleHeisenberg.sq_inner_le_of_center_moving
#audit_axioms GroupApproximation.EJZAngleHeisenberg.sq_inner_le_heisenberg
#audit_axioms GroupApproximation.EJZAngleHeisenberg.abs_inner_le_of_sq
#audit_axioms GroupApproximation.EJZAngleHeisenberg.movingAngleLE_heisenberg
