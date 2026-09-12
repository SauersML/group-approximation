import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationShort
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationGermGamma
import GroupApproximation.GroupTheory.AscendingHNNRecognition
import GroupApproximation.Meta.AxiomGuard

/-!
# `Υ_{Γ₂}([a, a + 1])` is an ascending HNN extension of `F_6`

Hyde–Lodha, proof of Lemma 4.5, second case: "Now assume that `b = a + 1`.  From Lemma 4.3, find
`f ∈ Υ_{Γ_n}([a, b])` such that `a·f'_+ = η_n`.  Let `c ∈ (a, b) ∩ ℤ[1/η_n]` be such that `x·f > x`
for all `x ∈ (a, c]`.  From Lemma 2.4, `Υ_{Γ_n}([a, b]) = ⟨f, Υ_{Γ_n}([c, b])⟩` is an ascending HNN
extension with base group `Υ_{Γ_n}([c, b]) ≅ F_{η_n}` ..., hence is of type `F_∞`."

Here only finite presentation is proved, through `AscendingHNNRecognition.isFinitelyPresented_of_ascending`:

* the base `Υ_{Γ₂}([c, a + 1])`, `c = a + 6^{-L}`, is finitely presented
  (`isFinitelyPresented_upsilon_gammaTwo_short`);
* `f` is `t ↦ a + 6 (t - a)` near `a⁺` (`exists_upsilon_gammaTwo_germLeft`), so `f` maps `[c, a + 1]`
  into itself, and no nonzero power of `f` fixes `(a, c)`;
* generation: an element `k` has germ `6^i` at `a⁺` (`exists_germLeft_of_fix`), `f^{-i} k` is the
  identity just right of `a`, and a power of `f` conjugates it into the base
  (`germLeft_iterate_ge`).

`isFinitelyPresented_upsilon_gammaTwo_long` moves any grid point `a` into `(0, 1)` first.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

theorem not_mem_perIoo_self {a b : ℚ} (hba : b ≤ a + 1) : a ∉ perIoo a b := by
  rintro ⟨k, hk1, hk2⟩
  rcases le_or_gt k 0 with hk | hk
  · have hk' : (k : ℚ) ≤ 0 := by exact_mod_cast hk
    linarith
  · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith

/-- **Hyde–Lodha, Lemma 4.5, second case**, in the unit frame. -/
theorem isFinitelyPresented_upsilon_gammaTwo_long_unit {a : ℚ} (ha : ∃ M, a ∈ Grid 6 M)
    (h0a : 0 < a) (ha1 : a < 1) : Group.IsFinitelyPresented ↥(upsilon gammaTwo a (a + 1)) := by
  -- the germ element `f`
  obtain ⟨f, hfU, ε, hfg⟩ := exists_upsilon_gammaTwo_germLeft ha h0a.le (δ := 1 - a)
    (by linarith) (by linarith)
  obtain ⟨hfΓ, hfs⟩ := mem_upsilon.mp hfU
  have hfs' : SupportedIn f (perIoo a (a + 1)) := hfs.mono (perIoo_mono le_rfl (by linarith))
  have hfG : f ∈ upsilon gammaTwo a (a + 1) := mem_upsilon.mpr ⟨hfΓ, hfs'⟩
  have hfmono := gammaTwo_strictMono hfΓ
  have hfa1 : f (a + 1) = a + 1 := by
    have e := gammaTwo_add_int hfΓ a 1
    rw [hfs' a (not_mem_perIoo_self le_rfl)] at e
    exact_mod_cast e
  -- the grid point `c = a + λ`
  obtain ⟨L, -, hL⟩ := exists_level (m := 4) 0 (δ := min ε ((1 - a) / 2))
    (lt_min hfg.1 (by linarith))
  have hX := sixInv_pos L
  have hXε : ((((4 : ℕ) : ℚ) + 2) ^ L)⁻¹ ≤ ε := le_trans hL (min_le_left _ _)
  have hXa : ((((4 : ℕ) : ℚ) + 2) ^ L)⁻¹ ≤ (1 - a) / 2 := le_trans hL (min_le_right _ _)
  have hlamG : ((((4 : ℕ) : ℚ) + 2) ^ L)⁻¹ ∈ Grid (4 + 2) L := mTwoPow_inv_mem_grid 4 L
  generalize ((((4 : ℕ) : ℚ) + 2) ^ L)⁻¹ = lam at hX hXε hXa hlamG
  obtain ⟨Ma, hMa⟩ := ha
  have hcG : ∃ M, a + lam ∈ Grid 6 M :=
    ⟨max Ma L, grid_add (grid_mono (le_max_left Ma L) hMa) (grid_mono (le_max_right Ma L) hlamG)⟩
  have ha1G : ∃ M, a + 1 ∈ Grid 6 M := ⟨Ma, grid_add hMa (one_mem_grid_six Ma)⟩
  have hfc : f (a + lam) = a + 6 * lam := by
    rw [hfg.2 _ (by linarith) (by linarith), zpow_one, six_cast]
    ring
  -- the base
  have hle : upsilon gammaTwo (a + lam) (a + 1) ≤ upsilon gammaTwo a (a + 1) :=
    upsilon_mono le_rfl (perIoo_mono (by linarith) le_rfl)
  haveI := isFinitelyPresented_upsilon_gammaTwo_short hcG ha1G (by linarith) (by linarith)
  haveI : Group.IsFinitelyPresented ↥((upsilon gammaTwo (a + lam) (a + 1)).subgroupOf
      (upsilon gammaTwo a (a + 1))) :=
    Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  refine AscendingHNNRecognition.isFinitelyPresented_of_ascending
    ((upsilon gammaTwo (a + lam) (a + 1)).subgroupOf (upsilon gammaTwo a (a + 1)))
    (⟨f, hfG⟩ : ↥(upsilon gammaTwo a (a + 1)))⁻¹ ?_ ?_ ?_
  · -- `f` conjugates the base into itself
    intro h hh
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    show f⁻¹⁻¹ * (h : Equiv.Perm ℚ) * f⁻¹ ∈ upsilon gammaTwo (a + lam) (a + 1)
    rw [inv_inv]
    have hc := conj_mem_upsilon hfΓ (fun y hy => gammaTwo_normalized y hy f hfΓ) hh
    rw [hfa1, hfc] at hc
    exact upsilon_mono le_rfl (perIoo_mono (by linarith) le_rfl) hc
  · -- no nonzero power of `f` lies in the base
    intro n hn
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_zpow] at hn
    have hg : (((⟨f, hfG⟩ : ↥(upsilon gammaTwo a (a + 1)))⁻¹ : ↥(upsilon gammaTwo a (a + 1))) :
        Equiv.Perm ℚ) = f⁻¹ := rfl
    rw [hg, inv_zpow'] at hn
    obtain ⟨-, hns⟩ := mem_upsilon.mp hn
    obtain ⟨ε', hgerm⟩ := germLeft_zpow hfg (-n)
    have hμ : 0 < min ε' (lam / 2) := lt_min hgerm.1 (by linarith)
    have hμ1 := min_le_left ε' (lam / 2)
    have hμ2 := min_le_right ε' (lam / 2)
    have hp : a + min ε' (lam / 2) ∉ perIoo (a + lam) (a + 1) := by
      rintro ⟨k, hk1, hk2⟩
      rcases le_or_gt k 0 with hk | hk
      · have hk' : (k : ℚ) ≤ 0 := by exact_mod_cast hk
        linarith
      · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
        linarith
    have hfix := hns _ hp
    rw [hgerm.2 _ (by linarith) (by linarith)] at hfix
    have h6 : (((4 : ℕ) : ℚ) + 2) ^ (-n) = 1 := by
      have e : ((((4 : ℕ) : ℚ) + 2) ^ (-n) - 1) * min ε' (lam / 2) = 0 := by linarith
      rcases mul_eq_zero.mp e with h | h
      · linarith
      · linarith
    rw [six_cast] at h6
    have e23 : (2 : ℚ) ^ (-n) * (3 : ℚ) ^ (-n) = (6 : ℚ) ^ (-n) := by
      rw [← mul_zpow]
      norm_num
    have h23 := (zpow_two_mul_zpow_three_eq_one (e23.trans h6)).1
    omega
  · -- generation
    rw [eq_top_iff]
    rintro ⟨k, hkG⟩ -
    obtain ⟨hkΓ, hks⟩ := mem_upsilon.mp hkG
    have hka : k a = a := hks a (not_mem_perIoo_self le_rfl)
    obtain ⟨i, ε₁, hk1⟩ := exists_germLeft_of_fix hkΓ ⟨Ma, hMa⟩ h0a ha1 hka
    obtain ⟨ε₂, hfi⟩ := germLeft_zpow hfg (-i)
    obtain ⟨ε₃, hk0⟩ : ∃ ε₃ : ℚ, GermLeft 4 a 0 ε₃ (f ^ (-i) * k) :=
      ⟨_, by have h := hfi.mul hk1; rwa [neg_add_cancel] at h⟩
    have hε₄ : 0 < min ε₃ lam := lt_min hk0.1 hX
    have hk0' := hk0.mono hε₄ (min_le_left _ _)
    have hk₀U : f ^ (-i) * k ∈ upsilon gammaTwo (a + min ε₃ lam) (a + 1) :=
      mem_upsilon.mpr ⟨gammaTwo.mul_mem (gammaTwo.zpow_mem hfΓ _) hkΓ,
        supportedIn_of_germLeft_zero (gammaTwo.mul_mem (gammaTwo.zpow_mem hfΓ _) hkΓ) hk0'⟩
    obtain ⟨N, -, hN⟩ := exists_level (m := 4) 0 (δ := min ε₃ lam / lam) (div_pos hε₄ hX)
    rw [six_cast, le_div_iff₀ hX] at hN
    have h6N : (0 : ℚ) < 6 ^ N := pow_pos (by norm_num) N
    have hNl : lam ≤ 6 ^ N * min ε₃ lam := by
      calc lam = 6 ^ N * ((6 ^ N)⁻¹ * lam) := by rw [← mul_assoc, mul_inv_cancel₀ h6N.ne', one_mul]
        _ ≤ 6 ^ N * min ε₃ lam := mul_le_mul_of_nonneg_left hN h6N.le
    have hit := germLeft_iterate_ge hfg hfmono hX.le hXε hε₄.le N
    rw [min_eq_right hNl] at hit
    have hfN : f ^ N ∈ gammaTwo := gammaTwo.pow_mem hfΓ N
    have hk₁U : f ^ N * (f ^ (-i) * k) * (f ^ N)⁻¹ ∈ upsilon gammaTwo (a + lam) (a + 1) := by
      have hc := conj_mem_upsilon hfN (fun y hy => gammaTwo_normalized y hy _ hfN) hk₀U
      rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfa1 N] at hc
      exact upsilon_mono le_rfl (perIoo_mono hit le_rfl) hc
    have e : (⟨k, hkG⟩ : ↥(upsilon gammaTwo a (a + 1))) =
        (⟨f, hfG⟩ : ↥(upsilon gammaTwo a (a + 1))) ^ i *
          ((⟨f, hfG⟩ : ↥(upsilon gammaTwo a (a + 1))) ^ N)⁻¹ *
          (⟨f ^ N * (f ^ (-i) * k) * (f ^ N)⁻¹, hle hk₁U⟩ : ↥(upsilon gammaTwo a (a + 1))) *
          (⟨f, hfG⟩ : ↥(upsilon gammaTwo a (a + 1))) ^ N := by
      apply Subtype.ext
      show k = f ^ i * (f ^ N)⁻¹ * (f ^ N * (f ^ (-i) * k) * (f ^ N)⁻¹) * f ^ N
      group
    rw [e]
    have hgc : ((⟨f, hfG⟩ : ↥(upsilon gammaTwo a (a + 1))))⁻¹ ∈ Subgroup.closure
        (((upsilon gammaTwo (a + lam) (a + 1)).subgroupOf (upsilon gammaTwo a (a + 1)) :
          Set ↥(upsilon gammaTwo a (a + 1))) ∪ {(⟨f, hfG⟩ : ↥(upsilon gammaTwo a (a + 1)))⁻¹}) :=
      Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
    have hfc' := inv_mem hgc
    rw [inv_inv] at hfc'
    refine mul_mem (mul_mem (mul_mem (zpow_mem hfc' i) (inv_mem (pow_mem hfc' N)))
      (Subgroup.subset_closure (Or.inl ?_))) (pow_mem hfc' N)
    show (⟨f ^ N * (f ^ (-i) * k) * (f ^ N)⁻¹, hle hk₁U⟩ : ↥(upsilon gammaTwo a (a + 1))) ∈
      (upsilon gammaTwo (a + lam) (a + 1)).subgroupOf (upsilon gammaTwo a (a + 1))
    rw [Subgroup.mem_subgroupOf]
    exact hk₁U

/-- **Hyde–Lodha, Lemma 4.5, second case.** -/
theorem isFinitelyPresented_upsilon_gammaTwo_long {a : ℚ} (ha : ∃ M, a ∈ Grid 6 M) :
    Group.IsFinitelyPresented ↥(upsilon gammaTwo a (a + 1)) := by
  obtain ⟨M, hM⟩ := ha
  have hhalf : ∃ M', a + 1 / 2 ∈ Grid 6 M' :=
    ⟨max M 1, grid_add (grid_mono (le_max_left M 1) hM) (grid_mono (le_max_right M 1)
      ⟨3, by norm_num⟩)⟩
  obtain ⟨g, hg, j, hj0, hj1⟩ := exists_move_into_unit ⟨M, hM⟩ hhalf (by linarith) (by linarith)
  have hgmono := gammaTwo_strictMono hg
  have hlt := hgmono (show a < a + 1 / 2 by linarith)
  obtain ⟨Mg, hMg⟩ := gammaTwo_apply_grid hg ⟨M, hM⟩
  haveI := isFinitelyPresented_upsilon_gammaTwo_long_unit (a := g a + j)
    ⟨Mg, grid_add hMg (int_mem_grid Mg j)⟩ hj0 (by linarith)
  have hga1 : g (a + 1) = g a + 1 := by exact_mod_cast gammaTwo_add_int hg a 1
  have e : upsilon gammaTwo (g a + j) (g a + j + 1) = upsilon gammaTwo (g a) (g (a + 1)) := by
    rw [hga1, show g a + j + 1 = (g a + 1) + j by ring]
    exact upsilon_add_int gammaTwo (g a) (g a + 1) j
  haveI : Group.IsFinitelyPresented ↥(upsilon gammaTwo (g a) (g (a + 1))) :=
    Group.IsFinitelyPresented.equiv (MulEquiv.subgroupCongr e)
  exact Group.IsFinitelyPresented.equiv
    (upsilonConjEquiv qTwo_le_gammaTwo le_rfl hg a (a + 1)).symm

#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_gammaTwo_long_unit
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_gammaTwo_long

end HydeLodha
end GroupApproximation
