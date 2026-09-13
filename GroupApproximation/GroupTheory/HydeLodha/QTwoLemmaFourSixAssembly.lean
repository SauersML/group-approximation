import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixStatements
import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixGenerators
import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixTransfer
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationLong
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationStabK
import GroupApproximation.Meta.AxiomGuard

/-!
# Hyde–Lodha Lemma 4.6 from its dynamics

Hyde–Lodha, Lemma 4.6, makes `Υ_Γ(I)` of type `F_∞` for every `Q_n ≤ Γ ≤ Γ_n` and every interval `I`
with `|I| ≤ 1`.  Proposition 4.7 consumes finite presentation at grid endpoints for `n = 2`,
`UpsilonFinitelyPresented`.  Here it follows from `LemmaFourSixDynamicsStatement`.

* `lemmaFourSixCaseOne_of_dynamics`: `N = ⟨f, H⟩`, with `H = ⟨v_1, ..., v_6⟩ ≅ F_6`
  (`exists_twisted_generators`), is an ascending HNN extension of `H`, and the Claim
  "`Υ_{Γ_n}(I)' ⊆ ⋃_{n ∈ ℕ} f^n H f^{-n}`" puts `Υ_{Γ₂}(I)'` inside `N`.
* `|I| < 1`: the casing pair in the unit frame, moved into place, is
  `isFinitelyPresented_upsilon_short_of_caseOne` (`QTwoLemmaFourSixTransfer`).
* `isFinitelyPresented_upsilon_long_unit_of_caseOne`, `isFinitelyPresented_upsilon_long_of_caseOne`:
  `|I| = 1`.  As in the proof of Lemma 4.5 (`QTwoFinitePresentationLong`), `Υ_Γ([a, a + 1])` is an
  ascending HNN extension of `Υ_Γ([a + λ, a + 1])` by an element of `Υ_{Q₂}([a, a + λ₀])` with slope `6`
  at `a⁺`.
* `upsilonFinitelyPresented_of_caseOne`, `upsilonFinitelyPresented_of_dynamics`: Lemma 4.6.

Permutations compose right to left: the paper's `f^{-n} k f^n` is `f ^ n * k * (f ^ n)⁻¹`.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

/-! ## Case 1 -/

/-- **Hyde–Lodha, proof of Lemma 4.6, Case 1**, from the dynamics: `N = ⟨f, H⟩`. -/
theorem lemmaFourSixCaseOne_of_dynamics (hdyn : LemmaFourSixDynamicsStatement) :
    LemmaFourSixCaseOneStatement := by
  intro a b ha hb h0a hab hb1
  obtain ⟨f, hfU, ⟨_, hfg⟩, e₁, e₂, c, d, hc, hd, hae₁, he₁c, hcd, hde₂, he₂b, hfe₁, hfe₂, hcov,
    s, hsU, hs1, hs2⟩ := hdyn a b ha hb h0a hab hb1
  have hfΓ : f ∈ gammaTwo := qTwo_le_gammaTwo (mem_upsilon.mp hfU).1
  -- `H = ⟨v_1, ..., v_6⟩`
  obtain ⟨u, hu, hH⟩ := exists_twisted_generators hc hd (by linarith) hcd (by linarith)
  obtain ⟨H, hHFP, hH1, hHcomm⟩ : ∃ H : Subgroup (Equiv.Perm ℚ), Group.IsFinitelyPresented ↥H ∧
      H ≤ ⁅upsilon gammaTwo e₁ e₂, upsilon gammaTwo e₁ e₂⁆ ∧
      ⁅H, H⁆ = ⁅upsilon gammaTwo c d, upsilon gammaTwo c d⁆ := by
    obtain ⟨⟨eB⟩, hcomm⟩ := hH s hs1 hs2
    haveI : Finite (brownRels 4) := (brownRels_finite 4).to_subtype
    refine ⟨_, Group.IsFinitelyPresented.equiv eB, ?_, hcomm⟩
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hsi : s i ∈ upsilon gammaTwo e₁ e₂ := upsilon_mono qTwo_le_gammaTwo subset_rfl (hsU i)
    have hui : u i ∈ upsilon gammaTwo e₁ e₂ := by
      have h : u i ∈ upsilon gammaTwo c d := by
        rw [← hu]
        exact Subgroup.subset_closure ⟨i, rfl⟩
      exact upsilon_mono le_rfl (perIoo_mono he₁c.le hde₂.le) h
    show s i * (u i)⁻¹ * (s i)⁻¹ * u i ∈ ⁅upsilon gammaTwo e₁ e₂, upsilon gammaTwo e₁ e₂⁆
    have e : s i * (u i)⁻¹ * (s i)⁻¹ * u i = ⁅s i, (u i)⁻¹⁆ := by
      rw [commutatorElement_def, inv_inv]
    rw [e]
    exact Subgroup.commutator_mem_commutator hsi (inv_mem hui)
  have hHe : H ≤ upsilon gammaTwo e₁ e₂ := hH1.trans (commutator_le_self _)
  have hΥΓ : upsilon gammaTwo e₁ e₂ ≤ gammaTwo := fun y hy => (mem_upsilon.mp hy).1
  have hHU : H ≤ upsilon qTwo a b := fun x hx =>
    mem_upsilon.mpr ⟨Subgroup.commutator_mono hΥΓ hΥΓ (hH1 hx),
      (mem_upsilon.mp (hHe hx)).2.mono (perIoo_mono hae₁.le he₂b.le)⟩
  -- `f` conjugates `H` into `H' = Υ_{Γ₂}(J₀)'`
  have hconjH : ∀ h ∈ H, f * h * f⁻¹ ∈ H := by
    intro h hh
    have hm := Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom (hH1 hh)
    rw [Subgroup.map_commutator, map_conj_upsilon qTwo_le_gammaTwo le_rfl hfΓ e₁ e₂,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hm
    have hle : upsilon gammaTwo (f e₁) (f e₂) ≤ upsilon gammaTwo c d :=
      upsilon_mono le_rfl (perIoo_mono hfe₁ hfe₂)
    have h2 : f * h * f⁻¹ ∈ ⁅H, H⁆ := by
      rw [hHcomm]
      exact Subgroup.commutator_mono hle hle hm
    exact commutator_le_self H h2
  -- `N = ⟨f, H⟩`
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (Equiv.Perm ℚ),
      N = Subgroup.closure ((H : Set (Equiv.Perm ℚ)) ∪ {f}) := ⟨_, rfl⟩
  have hHN : H ≤ N := by
    rw [hNdef]
    exact fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hfN : f ∈ N := by
    rw [hNdef]
    exact Subgroup.subset_closure (Or.inr (Set.mem_singleton f))
  have hNU : N ≤ upsilon qTwo a b := by
    rw [hNdef, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hHU hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hfU
  haveI := hHFP
  haveI : Group.IsFinitelyPresented ↥(H.subgroupOf N) :=
    Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe hHN).symm
  have hNFP : Group.IsFinitelyPresented ↥N := by
    refine AscendingHNNRecognition.isFinitelyPresented_of_ascending (H.subgroupOf N)
      (⟨f, hfN⟩ : ↥N)⁻¹ ?_ ?_ ?_
    · -- `f` conjugates `H` into itself
      intro h hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      show f⁻¹⁻¹ * (h : Equiv.Perm ℚ) * f⁻¹ ∈ H
      rw [inv_inv]
      exact hconjH _ hh
    · -- no nonzero power of `f` lies in `H`
      intro n hn
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_zpow] at hn
      have hg : (((⟨f, hfN⟩ : ↥N)⁻¹ : ↥N) : Equiv.Perm ℚ) = f⁻¹ := rfl
      rw [hg, inv_zpow'] at hn
      obtain ⟨-, hns⟩ := mem_upsilon.mp (hHe hn)
      obtain ⟨ε', hgerm⟩ := germLeft_zpow hfg (-n)
      have hμ : 0 < min ε' ((e₁ - a) / 2) := lt_min hgerm.1 (by linarith)
      have hμ1 := min_le_left ε' ((e₁ - a) / 2)
      have hμ2 := min_le_right ε' ((e₁ - a) / 2)
      have hp : a + min ε' ((e₁ - a) / 2) ∉ perIoo e₁ e₂ := by
        rintro ⟨k, hk1, hk2⟩
        rcases le_or_gt k 0 with hk | hk
        · have hk' : (k : ℚ) ≤ 0 := by exact_mod_cast hk
          linarith
        · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
          linarith
      have hfix := hns _ hp
      rw [hgerm.2 _ (by linarith) (by linarith)] at hfix
      have h6 : (((4 : ℕ) : ℚ) + 2) ^ (-n) = 1 := by
        have e : ((((4 : ℕ) : ℚ) + 2) ^ (-n) - 1) * min ε' ((e₁ - a) / 2) = 0 := by linarith
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
      rintro x -
      have hle : Subgroup.closure ((H : Set (Equiv.Perm ℚ)) ∪ {f}) ≤
          (Subgroup.closure (((H.subgroupOf N : Subgroup ↥N) : Set ↥N) ∪
            {(⟨f, hfN⟩ : ↥N)⁻¹})).map N.subtype := by
        rw [Subgroup.closure_le]
        rintro z (hz | hz)
        · refine Subgroup.mem_map.mpr ⟨⟨z, hHN hz⟩, Subgroup.subset_closure (Or.inl ?_), rfl⟩
          show (⟨z, hHN hz⟩ : ↥N) ∈ H.subgroupOf N
          rw [Subgroup.mem_subgroupOf]
          exact hz
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          have hgc : (⟨f, hfN⟩ : ↥N)⁻¹ ∈ Subgroup.closure
              (((H.subgroupOf N : Subgroup ↥N) : Set ↥N) ∪ {(⟨f, hfN⟩ : ↥N)⁻¹}) :=
            Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
          have hfc := inv_mem hgc
          rw [inv_inv] at hfc
          exact Subgroup.mem_map.mpr ⟨⟨f, hfN⟩, hfc, rfl⟩
      have hx : (x : Equiv.Perm ℚ) ∈ Subgroup.closure ((H : Set (Equiv.Perm ℚ)) ∪ {f}) := by
        rw [← hNdef]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle hx)
      have e : y = x := Subtype.ext hyx
      rw [← e]
      exact hy
  -- `Υ_{Γ₂}(I)' ⊆ ⋃_n f^n H f^{-n}`
  refine ⟨N, hNFP, hNU, ?_⟩
  intro k hk
  obtain ⟨n, hn⟩ := hcov k (commutator_upsilon_le_upsilonc ha hb h0a hab hb1 hk)
  have hfG : f ∈ upsilon gammaTwo a b := upsilon_mono qTwo_le_gammaTwo subset_rfl hfU
  have h1 := pow_conj_mem_commutator_upsilon ha hb hc hd h0a (by linarith) hcd (by linarith) hb1
    hfG hk hn
  rw [← hHcomm] at h1
  have h2 : f ^ n * k * (f ^ n)⁻¹ ∈ N := hHN (commutator_le_self H h1)
  have e : k = (f ^ n)⁻¹ * (f ^ n * k * (f ^ n)⁻¹) * f ^ n := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (pow_mem hfN n)) h2) (pow_mem hfN n)

/-! ## `|I| = 1` -/

/-- **Hyde–Lodha, Lemma 4.6**, `|I| = 1`, in the unit frame. -/
theorem isFinitelyPresented_upsilon_long_unit_of_caseOne (h1 : LemmaFourSixCaseOneStatement)
    {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) {a : ℚ}
    (ha : ∃ M, a ∈ Grid 6 M) (h0a : 0 < a) (ha1 : a < 1) :
    Group.IsFinitelyPresented ↥(upsilon Γ a (a + 1)) := by
  have hnorm := normalized_of_qTwo_le hQ hΓ
  obtain ⟨Ma, hMa⟩ := ha
  -- a grid point `a + λ₀ ∈ (a, 1)`
  obtain ⟨L₀, -, hL₀⟩ := exists_level (m := 4) 0 (δ := (1 - a) / 2) (by linarith)
  have hX₀ := sixInv_pos L₀
  have hXa₀ : ((((4 : ℕ) : ℚ) + 2) ^ L₀)⁻¹ ≤ (1 - a) / 2 := hL₀
  have hlam₀G : ((((4 : ℕ) : ℚ) + 2) ^ L₀)⁻¹ ∈ Grid (4 + 2) L₀ := mTwoPow_inv_mem_grid 4 L₀
  generalize ((((4 : ℕ) : ℚ) + 2) ^ L₀)⁻¹ = lam₀ at hX₀ hXa₀ hlam₀G
  have hb₀G : ∃ M, a + lam₀ ∈ Grid 6 M :=
    ⟨max Ma L₀, grid_add (grid_mono (le_max_left Ma L₀) hMa) (grid_mono (le_max_right Ma L₀) hlam₀G)⟩
  -- the germ element `f ∈ Υ_{Q₂}([a, a + λ₀])`
  obtain ⟨f, hfU, ε, hfg, -⟩ :=
    exists_upsilon_qTwo_germs ⟨Ma, hMa⟩ hb₀G h0a (by linarith) (by linarith)
  obtain ⟨hfQ, hfs⟩ := mem_upsilon.mp hfU
  have hfΓ : f ∈ Γ := hQ hfQ
  have hfΓ₂ : f ∈ gammaTwo := hΓ hfΓ
  have hfs' : SupportedIn f (perIoo a (a + 1)) := hfs.mono (perIoo_mono le_rfl (by linarith))
  have hfG : f ∈ upsilon Γ a (a + 1) := mem_upsilon.mpr ⟨hfΓ, hfs'⟩
  have hfmono := gammaTwo_strictMono hfΓ₂
  have hfa1 : f (a + 1) = a + 1 := by
    have e := gammaTwo_add_int hfΓ₂ a 1
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
  have hcG : ∃ M, a + lam ∈ Grid 6 M :=
    ⟨max Ma L, grid_add (grid_mono (le_max_left Ma L) hMa) (grid_mono (le_max_right Ma L) hlamG)⟩
  have ha1G : ∃ M, a + 1 ∈ Grid 6 M := ⟨Ma, grid_add hMa (one_mem_grid_six Ma)⟩
  have hfc : f (a + lam) = a + 6 * lam := by
    rw [hfg.2 _ (by linarith) (by linarith), zpow_one, six_cast]
    ring
  -- the base
  have hle : upsilon Γ (a + lam) (a + 1) ≤ upsilon Γ a (a + 1) :=
    upsilon_mono le_rfl (perIoo_mono (by linarith) le_rfl)
  haveI := isFinitelyPresented_upsilon_short_of_caseOne h1 hQ hΓ hcG ha1G (by linarith)
    (by linarith)
  haveI : Group.IsFinitelyPresented ↥((upsilon Γ (a + lam) (a + 1)).subgroupOf
      (upsilon Γ a (a + 1))) :=
    Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  refine AscendingHNNRecognition.isFinitelyPresented_of_ascending
    ((upsilon Γ (a + lam) (a + 1)).subgroupOf (upsilon Γ a (a + 1)))
    (⟨f, hfG⟩ : ↥(upsilon Γ a (a + 1)))⁻¹ ?_ ?_ ?_
  · -- `f` conjugates the base into itself
    intro h hh
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    show f⁻¹⁻¹ * (h : Equiv.Perm ℚ) * f⁻¹ ∈ upsilon Γ (a + lam) (a + 1)
    rw [inv_inv]
    have hc := conj_mem_upsilon hfΓ₂ (fun y hy => hnorm y hy f hfΓ₂) hh
    rw [hfa1, hfc] at hc
    exact upsilon_mono le_rfl (perIoo_mono (by linarith) le_rfl) hc
  · -- no nonzero power of `f` lies in the base
    intro n hn
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_zpow] at hn
    have hg : (((⟨f, hfG⟩ : ↥(upsilon Γ a (a + 1)))⁻¹ : ↥(upsilon Γ a (a + 1))) :
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
    obtain ⟨i, ε₁, hk1⟩ := exists_germLeft_of_fix (hΓ hkΓ) ⟨Ma, hMa⟩ h0a ha1 hka
    obtain ⟨ε₂, hfi⟩ := germLeft_zpow hfg (-i)
    obtain ⟨ε₃, hk0⟩ : ∃ ε₃ : ℚ, GermLeft 4 a 0 ε₃ (f ^ (-i) * k) :=
      ⟨_, by have h := hfi.mul hk1; rwa [neg_add_cancel] at h⟩
    have hε₄ : 0 < min ε₃ lam := lt_min hk0.1 hX
    have hk0' := hk0.mono hε₄ (min_le_left _ _)
    have hk₀Γ : f ^ (-i) * k ∈ Γ := Γ.mul_mem (Γ.zpow_mem hfΓ _) hkΓ
    have hk₀U : f ^ (-i) * k ∈ upsilon Γ (a + min ε₃ lam) (a + 1) :=
      mem_upsilon.mpr ⟨hk₀Γ, supportedIn_of_germLeft_zero (hΓ hk₀Γ) hk0'⟩
    obtain ⟨N, -, hN⟩ := exists_level (m := 4) 0 (δ := min ε₃ lam / lam) (div_pos hε₄ hX)
    rw [six_cast, le_div_iff₀ hX] at hN
    have h6N : (0 : ℚ) < 6 ^ N := pow_pos (by norm_num) N
    have hNl : lam ≤ 6 ^ N * min ε₃ lam := by
      calc lam = 6 ^ N * ((6 ^ N)⁻¹ * lam) := by rw [← mul_assoc, mul_inv_cancel₀ h6N.ne', one_mul]
        _ ≤ 6 ^ N * min ε₃ lam := mul_le_mul_of_nonneg_left hN h6N.le
    have hit := germLeft_iterate_ge hfg hfmono hX.le hXε hε₄.le N
    rw [min_eq_right hNl] at hit
    have hfN : f ^ N ∈ gammaTwo := gammaTwo.pow_mem hfΓ₂ N
    have hk₁U : f ^ N * (f ^ (-i) * k) * (f ^ N)⁻¹ ∈ upsilon Γ (a + lam) (a + 1) := by
      have hc := conj_mem_upsilon hfN (fun y hy => hnorm y hy _ hfN) hk₀U
      rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfa1 N] at hc
      exact upsilon_mono le_rfl (perIoo_mono hit le_rfl) hc
    have e : (⟨k, hkG⟩ : ↥(upsilon Γ a (a + 1))) =
        (⟨f, hfG⟩ : ↥(upsilon Γ a (a + 1))) ^ i *
          ((⟨f, hfG⟩ : ↥(upsilon Γ a (a + 1))) ^ N)⁻¹ *
          (⟨f ^ N * (f ^ (-i) * k) * (f ^ N)⁻¹, hle hk₁U⟩ : ↥(upsilon Γ a (a + 1))) *
          (⟨f, hfG⟩ : ↥(upsilon Γ a (a + 1))) ^ N := by
      apply Subtype.ext
      show k = f ^ i * (f ^ N)⁻¹ * (f ^ N * (f ^ (-i) * k) * (f ^ N)⁻¹) * f ^ N
      group
    rw [e]
    have hgc : ((⟨f, hfG⟩ : ↥(upsilon Γ a (a + 1))))⁻¹ ∈ Subgroup.closure
        (((upsilon Γ (a + lam) (a + 1)).subgroupOf (upsilon Γ a (a + 1)) :
          Set ↥(upsilon Γ a (a + 1))) ∪ {(⟨f, hfG⟩ : ↥(upsilon Γ a (a + 1)))⁻¹}) :=
      Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
    have hfc' := inv_mem hgc
    rw [inv_inv] at hfc'
    refine mul_mem (mul_mem (mul_mem (zpow_mem hfc' i) (inv_mem (pow_mem hfc' N)))
      (Subgroup.subset_closure (Or.inl ?_))) (pow_mem hfc' N)
    show (⟨f ^ N * (f ^ (-i) * k) * (f ^ N)⁻¹, hle hk₁U⟩ : ↥(upsilon Γ a (a + 1))) ∈
      (upsilon Γ (a + lam) (a + 1)).subgroupOf (upsilon Γ a (a + 1))
    rw [Subgroup.mem_subgroupOf]
    exact hk₁U

/-- **Hyde–Lodha, Lemma 4.6**, `|I| = 1`. -/
theorem isFinitelyPresented_upsilon_long_of_caseOne (h1 : LemmaFourSixCaseOneStatement)
    {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) {a : ℚ}
    (ha : ∃ M, a ∈ Grid 6 M) : Group.IsFinitelyPresented ↥(upsilon Γ a (a + 1)) := by
  obtain ⟨M, hM⟩ := ha
  have hhalf : ∃ M', a + 1 / 2 ∈ Grid 6 M' :=
    ⟨max M 1, grid_add (grid_mono (le_max_left M 1) hM) (grid_mono (le_max_right M 1)
      ⟨3, by norm_num⟩)⟩
  obtain ⟨g, hg, j, hj0, hj1⟩ := exists_move_into_unit ⟨M, hM⟩ hhalf (by linarith) (by linarith)
  have hgmono := gammaTwo_strictMono hg
  have hlt := hgmono (show a < a + 1 / 2 by linarith)
  obtain ⟨Mg, hMg⟩ := gammaTwo_apply_grid hg ⟨M, hM⟩
  haveI := isFinitelyPresented_upsilon_long_unit_of_caseOne h1 hQ hΓ (a := g a + j)
    ⟨Mg, grid_add hMg (int_mem_grid Mg j)⟩ hj0 (by linarith)
  have hga1 : g (a + 1) = g a + 1 := by exact_mod_cast gammaTwo_add_int hg a 1
  have e : upsilon Γ (g a + j) (g a + j + 1) = upsilon Γ (g a) (g (a + 1)) := by
    rw [hga1, show g a + j + 1 = (g a + 1) + j by ring]
    exact upsilon_add_int Γ (g a) (g a + 1) j
  haveI : Group.IsFinitelyPresented ↥(upsilon Γ (g a) (g (a + 1))) :=
    Group.IsFinitelyPresented.equiv (MulEquiv.subgroupCongr e)
  exact Group.IsFinitelyPresented.equiv (upsilonConjEquiv hQ hΓ hg a (a + 1)).symm

/-! ## Lemma 4.6 -/

/-- **Hyde–Lodha, Lemma 4.6**, from Case 1. -/
theorem upsilonFinitelyPresented_of_caseOne (h1 : LemmaFourSixCaseOneStatement) :
    UpsilonFinitelyPresented := by
  intro Γ hQ hΓ a b ha hb hab hba
  rcases hba.lt_or_eq with hlt | rfl
  · exact isFinitelyPresented_upsilon_short_of_caseOne h1 hQ hΓ ha hb hab (by linarith)
  · exact isFinitelyPresented_upsilon_long_of_caseOne h1 hQ hΓ ha

/-- **Hyde–Lodha, Lemma 4.6**, from the dynamics of its proof. -/
theorem upsilonFinitelyPresented_of_dynamics (hdyn : LemmaFourSixDynamicsStatement) :
    UpsilonFinitelyPresented :=
  upsilonFinitelyPresented_of_caseOne (lemmaFourSixCaseOne_of_dynamics hdyn)

#audit_axioms GroupApproximation.HydeLodha.lemmaFourSixCaseOne_of_dynamics
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_long_unit_of_caseOne
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_long_of_caseOne
#audit_axioms GroupApproximation.HydeLodha.upsilonFinitelyPresented_of_caseOne
#audit_axioms GroupApproximation.HydeLodha.upsilonFinitelyPresented_of_dynamics

end HydeLodha
end GroupApproximation
