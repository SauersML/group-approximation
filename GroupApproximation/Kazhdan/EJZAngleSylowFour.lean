import GroupApproximation.Kazhdan.EJZAngleSylowFourGram
import GroupApproximation.Kazhdan.EJZAngleHeisenberg

/-!
# The representation angle `√(2/p)` of the Sylow subgroup `U₄(p)` of `Sp₄(F_p)`

Caprace--Conder--Kaluba--Witzel (arXiv:2011.09276), Proposition 7.3(ii): in
`U₄(p) = ⟨a, b | aᵖ, bᵖ, [a,b,a], [a,b,b,a], [a,b,b,b]⟩` the subgroups `⟨a⟩` and `⟨b⟩` make
representation angle `√(2/p)`.  Proved here without characters, from the relations alone
(`SylowFourData`), in every orthogonal representation of an ambient group.

Put `w = [a, b]`, `z = [w, b]`.  Let `x` be `a`-fixed and `y` be `b`-fixed and orthogonal to the
`⟨a⟩ ⊔ ⟨b⟩`-fixed vectors.  Split `x` along the fixed spaces of `⟨z⟩` and then of `⟨w⟩`, and `y`
along the fixed space of `⟨z⟩`:
* the part of `x` fixed by `w` and `z` is orthogonal to `y` (the translate sum over `⟨b⟩` is fixed by
  `a` and `b`);
* on the part fixed by `z` and moved by `w`, `(a, b)` behaves as a Heisenberg pair with commutator
  `w`, and the bound is `1/√p`;
* on the part moved by `z`, the Gram sum bound of `EJZAngleSylowFourGram` gives `‖T‖² ≤ 2p ‖x‖²`, so
  the bound is `√(2/p)`.
The three bounds combine by Cauchy--Schwarz to `p ⟪x, y⟫² ≤ 2 ‖x‖² ‖y‖²`.
-/

namespace GroupApproximation

universe u v

namespace EJZAngleSylowFour

open KazhdanFixedSpace EJZAngleTranslates EJZAngleBessel EJZAngleSylowFourGram EJZAngleHeisenberg

variable {G : Type u} [Group G]

/-- The relations of `U₄(p)` used for the angle, with `w = [a, b]` and `z = [w, b]` passed as data,
together with the two transversality tables of `EJZAngleSylowFourGram.gram_sum_le_sylowFour`. -/
structure SylowFourData (p : ℕ) (a b w z : G) : Prop where
  prime : p.Prime
  hab : a * b = b * a * w
  hwb : w * b = b * w * z
  hwa : Commute w a
  hza : Commute z a
  hzb : Commute z b
  hzw : Commute z w
  hb : b ^ p = 1
  hw : w ^ p = 1
  hz : z ^ p = 1
  tableT : ∀ i ∈ (Finset.range p).erase 0, ∀ j ∈ (Finset.range p).erase 0, i ≠ j →
    ∃ α β : ℕ, (i * α + j * β) % p = 0 ∧ (triangular i * α + triangular j * β) % p = 1
  tableS : ∀ i ∈ (Finset.range p).erase 0, ∀ j ∈ (Finset.range p).erase 0, i ≠ j →
    ∃ α β : ℕ, (i * α + j * β) % p = 0 ∧
      ((triangular i + i * (p - i)) * α + (triangular j + j * (p - j)) * β) % p = 1

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A vector fixed by `w` and `z` is fixed by `wᵐ z^c`. -/
theorem coord_apply_of_fixed (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {w z : G} {u : E} (huw : ρ w u = u)
    (huz : ρ z u = u) (i j : ℕ) : ρ (w ^ i * z ^ j) u = u := by
  rw [map_mul]
  change ρ (w ^ i) (ρ (z ^ j) u) = u
  rw [pow_apply_of_fixed ρ huz j, pow_apply_of_fixed ρ huw i]

/-- A real inequality combining two angle bounds by Cauchy--Schwarz. -/
theorem sq_add_le_of_sq_le {p A B a b c d : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hA : p * A ^ 2 ≤ 2 * a ^ 2 * c ^ 2)
    (hB : p * B ^ 2 ≤ 2 * b ^ 2 * d ^ 2) :
    p * (A + B) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have hA0 : 0 ≤ p * A ^ 2 := mul_nonneg hp.le (sq_nonneg A)
  have hB0 : 0 ≤ p * B ^ 2 := mul_nonneg hp.le (sq_nonneg B)
  have hprod : (p * (A * B)) ^ 2 ≤ (2 * (a * c) * (b * d)) ^ 2 := by
    calc
      (p * (A * B)) ^ 2 = (p * A ^ 2) * (p * B ^ 2) := by ring
      _ ≤ (2 * a ^ 2 * c ^ 2) * (2 * b ^ 2 * d ^ 2) := mul_le_mul hA hB hB0 (by positivity)
      _ = (2 * (a * c) * (b * d)) ^ 2 := by ring
  have hAB : p * (A * B) ≤ 2 * (a * c) * (b * d) :=
    (abs_le_of_sq_le_sq hprod
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg ha hc)) (mul_nonneg hb hd))).trans'
      (le_abs_self _)
  nlinarith [sq_nonneg (a * d - b * c)]

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Part fixed by `w` and `z`.** -/
theorem inner_eq_zero_of_wz_fixed (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} {a b w z : G}
    (hd : SylowFourData p a b w z) {u y : E} (hua : ρ a u = u) (huw : ρ w u = u)
    (huz : ρ z u = u) (hyb : ρ b y = y)
    (hyL : y ∈ (fixedSubspace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b))ᗮ) :
    inner ℝ u y = 0 := by
  have hTa : ρ a (translateSum ρ b p u) = translateSum ρ b p u := by
    unfold translateSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [apply_translate_sylowFour ρ hd.hab hd.hwb hd.hzw hd.hzb hd.hwa hd.hza m hua,
      coord_apply_of_fixed ρ huw huz]
  have hTb : ρ b (translateSum ρ b p u) = translateSum ρ b p u := translateSum_fixed ρ hd.hb u
  have hTL : translateSum ρ b p u ∈ fixedSubspace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    rw [fixedSubspace_sup]
    exact ⟨(mem_fixedSubspace_zpowers_iff ρ a _).mpr hTa,
      (mem_fixedSubspace_zpowers_iff ρ b _).mpr hTb⟩
  have hzero : inner ℝ (translateSum ρ b p u) y = 0 :=
    Submodule.inner_right_of_mem_orthogonal hTL hyL
  rw [inner_translateSum_of_fixed ρ b p u hyb] at hzero
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hd.prime.pos.ne'
  exact (mul_eq_zero.mp hzero).resolve_left hp'

/-- **Part fixed by `z` and moved by `w`: the bound `1/√p`.** -/
theorem sq_inner_le_of_z_fixed (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} {a b w z : G}
    (hd : SylowFourData p a b w z) {u y : E} (hua : ρ a u = u) (huz : ρ z u = u)
    (huW : u ∈ (fixedSubspace ρ (Subgroup.zpowers w))ᗮ) (hyb : ρ b y = y) :
    (p : ℝ) * inner ℝ u y ^ 2 ≤ ‖u‖ ^ 2 * ‖y‖ ^ 2 := by
  have hp0 : 0 < p := hd.prime.pos
  have htwist : ∀ m : ℕ, ρ a (ρ (b ^ m) u) = ρ (w ^ m) (ρ (b ^ m) u) := by
    intro m
    rw [apply_translate_sylowFour ρ hd.hab hd.hwb hd.hzw hd.hzb hd.hwa hd.hza m hua, map_mul]
    change ρ (b ^ m) (ρ (w ^ m) (ρ (z ^ triangular m) u)) = ρ (w ^ m) (ρ (b ^ m) u)
    rw [pow_apply_of_fixed ρ huz]
    have h := congrArg (fun q ↦ ρ q u) (pow_mul_pow_eq_of_commutator hd.hwb hd.hzw hd.hzb m m)
    simp only [map_mul] at h
    change ρ (w ^ m) (ρ (b ^ m) u) = ρ (b ^ m) (ρ (w ^ m) (ρ (z ^ (m * m)) u)) at h
    rw [pow_apply_of_fixed ρ huz] at h
    exact h.symm
  have hgram : ∀ m ∈ Finset.range p, m ≠ 0 → inner ℝ u (ρ (b ^ m) u) = 0 := by
    intro m hm hm0
    have hmp : m < p := Finset.mem_range.mp hm
    have hcop : Nat.Coprime m p :=
      ((Nat.Prime.coprime_iff_not_dvd hd.prime).mpr
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm0) hmp)).symm
    exact inner_eq_zero_of_twisted ρ hp0 hd.hw hd.hwa.symm
      (exists_pow_mul_eq_pow hd.hw hp0.ne' hcop) hua (htwist m) huW
  have hsum : ∑ m ∈ Finset.range p, inner ℝ u (ρ (b ^ m) u) = ‖u‖ ^ 2 := by
    rw [Finset.sum_eq_single 0 hgram (fun h ↦ absurd (Finset.mem_range.mpr hp0) h)]
    simp
  have hT := norm_sq_translateSum ρ hd.hb u
  rw [hsum] at hT
  have hcs := sq_inner_le_of_translateSum ρ b p u hyb
  rw [hT] at hcs
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp0
  have h3 : (p : ℝ) * ((p : ℝ) * inner ℝ u y ^ 2) ≤ (p : ℝ) * (‖u‖ ^ 2 * ‖y‖ ^ 2) := by
    nlinarith [hcs]
  exact le_of_mul_le_mul_left h3 hppos

omit [CompleteSpace E] in
/-- **Part moved by `z`: the bound `√(2/p)`.** -/
theorem sq_inner_le_of_z_moving (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} {a b w z : G}
    (hd : SylowFourData p a b w z) {u y : E} (hua : ρ a u = u)
    (huz : ∀ g : E, ρ z g = g → inner ℝ u g = 0) (hyb : ρ b y = y) :
    (p : ℝ) * inner ℝ u y ^ 2 ≤ 2 * ‖u‖ ^ 2 * ‖y‖ ^ 2 := by
  have hp0 : 0 < p := hd.prime.pos
  have hgram := gram_sum_le_sylowFour ρ hp0 hd.hab hd.hwb hd.hwa hd.hza hd.hzb hd.hzw hd.hb
    hd.hw hd.hz hd.tableT hd.tableS hua huz
  have hsplit : inner ℝ u (ρ (b ^ 0) u) +
      ∑ m ∈ (Finset.range p).erase 0, inner ℝ u (ρ (b ^ m) u) =
        ∑ m ∈ Finset.range p, inner ℝ u (ρ (b ^ m) u) :=
    Finset.add_sum_erase _ _ (Finset.mem_range.mpr hp0)
  have h0 : inner ℝ u (ρ (b ^ 0) u) = ‖u‖ ^ 2 := by simp
  have hsum : ∑ m ∈ Finset.range p, inner ℝ u (ρ (b ^ m) u) ≤ 2 * ‖u‖ ^ 2 := by
    rw [← hsplit, h0]
    linarith
  have hT := norm_sq_translateSum ρ hd.hb u
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp0
  have hT2 : ‖translateSum ρ b p u‖ ^ 2 ≤ (p : ℝ) * (2 * ‖u‖ ^ 2) := by
    rw [hT]
    exact mul_le_mul_of_nonneg_left hsum hppos.le
  have hcs := sq_inner_le_of_translateSum ρ b p u hyb
  have h3 : (p : ℝ) * ((p : ℝ) * inner ℝ u y ^ 2) ≤ (p : ℝ) * (2 * ‖u‖ ^ 2 * ‖y‖ ^ 2) := by
    nlinarith [hcs, hT2, sq_nonneg ‖y‖]
  exact le_of_mul_le_mul_left h3 hppos

/-- **The `U₄(p)` angle.**  If `x` is `a`-fixed, `y` is `b`-fixed and orthogonal to the
`⟨a⟩ ⊔ ⟨b⟩`-fixed vectors, then `p ⟪x, y⟫² ≤ 2 ‖x‖² ‖y‖²`. -/
theorem sq_inner_le_sylowFour (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} {a b w z : G}
    (hd : SylowFourData p a b w z) (hzL : z ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    {x y : E} (hx : ρ a x = x) (hy : ρ b y = y)
    (hym : y ∈ subgroupMovingSubspace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) :
    (p : ℝ) * inner ℝ x y ^ 2 ≤ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hd.prime.pos
  have hZL : Subgroup.zpowers z ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.zpowers_le.mpr hzL
  haveI : CompleteSpace (fixedSubspace ρ (Subgroup.zpowers z)) :=
    (isClosed_fixedSubspace ρ _).completeSpace_coe
  -- split `x` and `y` along `⟨z⟩`
  obtain ⟨hx0a, hx3a⟩ := projections_fixed (mem_normalizer_zpowers hd.hza) ρ hx
  obtain ⟨hy0b, hy3b⟩ := projections_fixed (mem_normalizer_zpowers hd.hzb) ρ hy
  have hx0z : ρ z (fixedProjection ρ (Subgroup.zpowers z) x : E) =
      fixedProjection ρ (Subgroup.zpowers z) x :=
    (mem_fixedSubspace_zpowers_iff ρ _ _).mp (fixedProjection ρ _ x).2
  -- split the `z`-fixed part of `x` along `⟨w⟩`
  obtain ⟨hx1a, hx2a⟩ := projections_fixed (mem_normalizer_zpowers hd.hwa) ρ hx0a
  obtain ⟨hx1z, hx2z⟩ := projections_fixed (mem_normalizer_zpowers hd.hzw.symm) ρ hx0z
  haveI : CompleteSpace (fixedSubspace ρ (Subgroup.zpowers w)) :=
    (isClosed_fixedSubspace ρ _).completeSpace_coe
  have hx1w : ρ w (fixedProjection ρ (Subgroup.zpowers w)
      (fixedProjection ρ (Subgroup.zpowers z) x : E) : E) =
      fixedProjection ρ (Subgroup.zpowers w) (fixedProjection ρ (Subgroup.zpowers z) x : E) :=
    (mem_fixedSubspace_zpowers_iff ρ _ _).mp (fixedProjection ρ _ _).2
  have hy0L : (fixedProjection ρ (Subgroup.zpowers z) y : E) ∈
      (fixedSubspace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro g hg
    have hgZ : (fixedSubspace ρ (Subgroup.zpowers z)).starProjection g = g :=
      Submodule.starProjection_eq_self_iff.mpr (KazhdanFixedSpace.antitone ρ hZL hg)
    change inner ℝ g ((fixedSubspace ρ (Subgroup.zpowers z)).starProjection y) = 0
    rw [← Submodule.inner_starProjection_left_eq_right, hgZ]
    exact Submodule.inner_right_of_mem_orthogonal hg hym
  have hx3z : ∀ g : E, ρ z g = g →
      inner ℝ (subgroupMovingProjection ρ (Subgroup.zpowers z) x) g = 0 := by
    intro g hg
    have hgZ : g ∈ fixedSubspace ρ (Subgroup.zpowers z) := (mem_fixedSubspace_zpowers_iff ρ z g).mpr hg
    exact Submodule.inner_left_of_mem_orthogonal hgZ (subgroupMovingProjection_mem ρ _ x)
  -- the three pieces
  have hi := inner_eq_zero_of_wz_fixed ρ hd hx1a hx1w hx1z hy0b hy0L
  have hii := sq_inner_le_of_z_fixed ρ hd hx2a hx2z (subgroupMovingProjection_mem ρ _ _) hy0b
  have hiii := sq_inner_le_of_z_moving ρ hd hx3a hx3z hy3b
  -- assemble
  have hsplitZ := inner_eq_fixed_add_moving ρ (Subgroup.zpowers z) x y
  have hsplitW := inner_eq_fixed_add_moving ρ (Subgroup.zpowers w)
    (fixedProjection ρ (Subgroup.zpowers z) x : E) (fixedProjection ρ (Subgroup.zpowers z) y : E)
  have hx0dec : (fixedProjection ρ (Subgroup.zpowers z) x : E) =
      (fixedProjection ρ (Subgroup.zpowers w) (fixedProjection ρ (Subgroup.zpowers z) x : E) : E) +
        subgroupMovingProjection ρ (Subgroup.zpowers w) (fixedProjection ρ (Subgroup.zpowers z) x : E) := by
    rw [subgroupMovingProjection_eq_sub_fixedProjection]
    abel
  have hinner0 : inner ℝ (fixedProjection ρ (Subgroup.zpowers z) x : E)
      (fixedProjection ρ (Subgroup.zpowers z) y : E) =
      inner ℝ (subgroupMovingProjection ρ (Subgroup.zpowers w)
        (fixedProjection ρ (Subgroup.zpowers z) x : E))
        (fixedProjection ρ (Subgroup.zpowers z) y : E) := by
    conv_lhs => rw [hx0dec]
    rw [inner_add_left, hi, zero_add]
  have hxy : inner ℝ x y =
      inner ℝ (subgroupMovingProjection ρ (Subgroup.zpowers w)
        (fixedProjection ρ (Subgroup.zpowers z) x : E))
        (fixedProjection ρ (Subgroup.zpowers z) y : E) +
      inner ℝ (subgroupMovingProjection ρ (Subgroup.zpowers z) x)
        (subgroupMovingProjection ρ (Subgroup.zpowers z) y) := by
    rw [hsplitZ, hinner0]
  have hnx := norm_sq_fixedProjection_add_movingProjection ρ (Subgroup.zpowers z) x
  have hny := norm_sq_fixedProjection_add_movingProjection ρ (Subgroup.zpowers z) y
  have hx2le := pow_le_pow_left₀ (norm_nonneg _)
    (norm_subgroupMovingProjection_le ρ (Subgroup.zpowers w)
      (fixedProjection ρ (Subgroup.zpowers z) x : E)) 2
  have hii' : (p : ℝ) * inner ℝ (subgroupMovingProjection ρ (Subgroup.zpowers w)
        (fixedProjection ρ (Subgroup.zpowers z) x : E))
        (fixedProjection ρ (Subgroup.zpowers z) y : E) ^ 2 ≤
      2 * ‖subgroupMovingProjection ρ (Subgroup.zpowers w)
        (fixedProjection ρ (Subgroup.zpowers z) x : E)‖ ^ 2 *
        ‖(fixedProjection ρ (Subgroup.zpowers z) y : E)‖ ^ 2 := by
    nlinarith [hii, sq_nonneg (‖subgroupMovingProjection ρ (Subgroup.zpowers w)
      (fixedProjection ρ (Subgroup.zpowers z) x : E)‖ * ‖(fixedProjection ρ (Subgroup.zpowers z) y : E)‖)]
  have hcomb := sq_add_le_of_sq_le hppos (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hii' hiii
  rw [hxy]
  refine hcomb.trans ?_
  have hxle : ‖subgroupMovingProjection ρ (Subgroup.zpowers w)
      (fixedProjection ρ (Subgroup.zpowers z) x : E)‖ ^ 2 +
      ‖subgroupMovingProjection ρ (Subgroup.zpowers z) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    linarith
  have hyeq : ‖(fixedProjection ρ (Subgroup.zpowers z) y : E)‖ ^ 2 +
      ‖subgroupMovingProjection ρ (Subgroup.zpowers z) y‖ ^ 2 = ‖y‖ ^ 2 := hny.symm
  rw [hyeq]
  have hy2 : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
  nlinarith [hxle, hy2]

omit [CompleteSpace E] in
/-- From `p ⟪x, y⟫² ≤ 2 ‖x‖² ‖y‖²` and `2 ≤ p ε²` to `|⟪x, y⟫| ≤ ε ‖x‖ ‖y‖`. -/
theorem abs_inner_le_of_sq_two {p : ℕ} {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (hpe : 2 ≤ (p : ℝ) * epsilon ^ 2) {x y : E}
    (h : (p : ℝ) * inner ℝ x y ^ 2 ≤ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2) :
    |inner ℝ x y| ≤ epsilon * ‖x‖ * ‖y‖ := by
  have hsq : inner ℝ x y ^ 2 ≤ (epsilon * ‖x‖ * ‖y‖) ^ 2 := by
    have hi : 0 ≤ inner ℝ x y ^ 2 := sq_nonneg _
    have h2 : 2 * inner ℝ x y ^ 2 ≤ 2 * (epsilon * ‖x‖ * ‖y‖) ^ 2 := by
      calc
        2 * inner ℝ x y ^ 2 ≤ ((p : ℝ) * epsilon ^ 2) * inner ℝ x y ^ 2 := by nlinarith
        _ = epsilon ^ 2 * ((p : ℝ) * inner ℝ x y ^ 2) := by ring
        _ ≤ epsilon ^ 2 * (2 * ‖x‖ ^ 2 * ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
        _ = 2 * (epsilon * ‖x‖ * ‖y‖) ^ 2 := by ring
    linarith
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  exact hsq

end EJZAngleSylowFour

/-- **Moving angle of a `U₄(p)` pair** (CCKW Proposition 7.3(ii), character-free). -/
theorem EJZAngleSylowFour.movingAngleLE_sylowFour {G : Type u} [Group G] {p : ℕ} {a b w z : G}
    (hd : EJZAngleSylowFour.SylowFourData p a b w z)
    (hzL : z ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (hpe : 2 ≤ (p : ℝ) * epsilon ^ 2) :
    ThreeVertexKazhdan.MovingAngleLE.{u, v} (Subgroup.zpowers a) (Subgroup.zpowers b) epsilon := by
  intro E _ _ _ ρ x y hx hy _hxm hym
  have hx' : ρ a x = x := (EJZAngleTranslates.mem_fixedSubspace_zpowers_iff ρ a x).mp hx
  have hy' : ρ b y = y := (EJZAngleTranslates.mem_fixedSubspace_zpowers_iff ρ b y).mp hy
  exact EJZAngleSylowFour.abs_inner_le_of_sq_two heps hpe
    (EJZAngleSylowFour.sq_inner_le_sylowFour ρ hd hzL hx' hy' hym)

end GroupApproximation

#audit_axioms GroupApproximation.EJZAngleSylowFour.coord_apply_of_fixed
#audit_axioms GroupApproximation.EJZAngleSylowFour.sq_add_le_of_sq_le
#audit_axioms GroupApproximation.EJZAngleSylowFour.inner_eq_zero_of_wz_fixed
#audit_axioms GroupApproximation.EJZAngleSylowFour.sq_inner_le_of_z_fixed
#audit_axioms GroupApproximation.EJZAngleSylowFour.sq_inner_le_of_z_moving
#audit_axioms GroupApproximation.EJZAngleSylowFour.sq_inner_le_sylowFour
#audit_axioms GroupApproximation.EJZAngleSylowFour.abs_inner_le_of_sq_two
#audit_axioms GroupApproximation.EJZAngleSylowFour.movingAngleLE_sylowFour
