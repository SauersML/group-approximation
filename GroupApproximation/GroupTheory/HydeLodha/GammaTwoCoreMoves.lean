import GroupApproximation.GroupTheory.HydeLodha.GammaTwoPeriodic
import GroupApproximation.GroupTheory.HydeLodha.GammaTwoStabilizer
import GroupApproximation.GroupTheory.HydeLodha.PeriodicDisplacement
import GroupApproximation.Meta.AxiomGuard

/-!
# Moves by the periodic core inside `Γ₂`

The steps of Hyde–Lodha's Lemma 3.9 that involve only the `1`-periodic copy of `F_6'`, for `n = 2`.
Throughout, `⁅perCore 4, perCore 4⁆` is the periodic copy of `F_6'` (`PeriodicCore`).

* `perCore_le_gammaTwo`, `commutator_perCore_le_gammaTwo`: `F_6' ≤ Q₂ = ⁅Γ₂, Γ₂⁆`.
* `not_translation_of_mem_gammaTwo`: a nontrivial element of `Γ₂` is not a translation by an integer
  (condition (3) at a point outside `ℤ[1/6]`).
* `commutator_perCore_le_of_ne_bot`, Lemma 3.9(1): a nontrivial subgroup `N ≤ Γ ≤ Γ₂` normalized by
  `Γ ⊇ F_6'` contains `F_6'`.
* `exists_perCore_apply`: `F_6'` moves a point of `ℤ[1/6] ∩ (0, 1)` to any point of `(0, 1)` in the same
  residue class modulo `5 ℤ[1/6]` (Proposition 3.5 for one point).
* `exists_mem_unit_of_not_int`, Lemma 3.9(2): if `N ⊇ F_6'` is normalized by an `h ∈ Γ₂` with
  `h 0 ∉ ℤ`, then some `g ∈ N` has `0 < g 0 < 1`.  Here `g = ⁅h, P⁆` for a `P ∈ F_6'` pushing the
  fractional part of `h⁻¹ 0` upwards; no appeal to minimality is needed.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

theorem perCore_le_gammaTwo : perCore 4 ≤ gammaTwo := by
  rintro _ ⟨x, -, rfl⟩
  exact perHom_mem_gammaTwo x

theorem commutator_perCore_le_gammaTwo : ⁅perCore 4, perCore 4⁆ ≤ ⁅gammaTwo, gammaTwo⁆ :=
  Subgroup.commutator_mono perCore_le_gammaTwo perCore_le_gammaTwo

theorem perHom_apply_intCast (a : ↥(compactF 4 1)) (k : ℤ) : perHom 4 a k = k := by
  have h := perHom_add_int 4 a 0 k
  rw [zero_add] at h
  rw [h, perHom_apply_of_mem 4 a le_rfl zero_lt_one, compactF_fix_nonpos a.2 le_rfl, zero_add]

theorem gammaTwo_apply_grid {f : Equiv.Perm ℚ} (hf : f ∈ gammaTwo) {x : ℚ}
    (hx : ∃ M, x ∈ Grid 6 M) : ∃ M, f x ∈ Grid 6 M := by
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, -, -⟩ := mem_gammaTwo.mp hf
  obtain ⟨M, hM⟩ := hx
  exact ⟨_, hA.mapsGrid hM⟩

theorem fract_grid {x : ℚ} (hx : ∃ M, x ∈ Grid 6 M) : ∃ M, Int.fract x ∈ Grid 6 M := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨M, ?_⟩
  rw [← Int.self_sub_floor]
  exact grid_sub hM (int_mem_grid M _)

theorem zero_mem_grid_six : ∃ M, (0 : ℚ) ∈ Grid 6 M := ⟨0, 0, by norm_num⟩

/-- **A nontrivial element of `Γ₂` is not an integer translation.** -/
theorem not_translation_of_mem_gammaTwo {f : Equiv.Perm ℚ} (hf : f ∈ gammaTwo) (hf1 : f ≠ 1) :
    ∀ k : ℤ, ∃ t : ℚ, f t ≠ t + k := by
  intro k
  by_contra hall
  have hall' : ∀ t : ℚ, f t = t + k := fun t => by
    by_contra h
    exact hall ⟨t, h⟩
  obtain ⟨-, -, hc⟩ := mem_gammaTwo.mp hf
  obtain ⟨a, b, i, j, hax, hxb, haff, hij⟩ := hc _ (not_dyadic6_gridPt_add_fifth 0 0)
  have hk : k = 0 := int_eq_zero_of_affineOn_translation hall' hax hxb haff hij
  apply hf1
  ext t
  rw [hall' t, hk]
  simp

/-- **Hyde–Lodha, Lemma 3.9(1).** -/
theorem commutator_perCore_le_of_ne_bot (Γ N : Subgroup (Equiv.Perm ℚ)) (hΓ : Γ ≤ gammaTwo)
    (hcore : ⁅perCore 4, perCore 4⁆ ≤ Γ) (hNΓ : N ≤ Γ)
    (hN : ∀ n ∈ N, ∀ g ∈ Γ, g * n * g⁻¹ ∈ N) (hne : N ≠ ⊥) : ⁅perCore 4, perCore 4⁆ ≤ N := by
  obtain ⟨⟨f, hfN⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  have hfΓ : f ∈ gammaTwo := hΓ (hNΓ hfN)
  exact commutator_perCore_le_of_periodic 4 N (fun n hn g hg => hN n hn g (hcore hg)) hfN
    (gammaTwo_strictMono hfΓ) (mem_gammaTwo.mp hfΓ).2.1 (not_translation_of_mem_gammaTwo hfΓ hf1')

/-- `F_6'` acts transitively on each residue class of `ℤ[1/6] ∩ (0, 1)`. -/
theorem exists_perCore_apply {x y : ℚ} (hx : ∃ M, x ∈ Grid (4 + 2) M)
    (hy : ∃ M, y ∈ Grid (4 + 2) M) (hres : ResEq 4 y x) (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y)
    (hy1 : y < 1) :
    ∃ a : ↥(compactF 4 1), perHom 4 a ∈ ⁅perCore 4, perCore 4⁆ ∧ perHom 4 a x = y := by
  obtain ⟨p, hp, hpx⟩ := exists_commutator_compactCore_apply (m := 4) hx hy hres hx0 hx1 hy0 hy1
  refine ⟨⟨p, compactCore_le (commutator_le_self _ hp)⟩,
    perHom_mem_commutator_perCore 4 (x := ⟨p, compactCore_le (commutator_le_self _ hp)⟩) hp, ?_⟩
  rw [perHom_apply_of_mem 4 _ hx0.le hx1]
  exact hpx

/-- **Hyde–Lodha, Lemma 3.9(2)**, without minimality. -/
theorem exists_mem_unit_of_not_int (N : Subgroup (Equiv.Perm ℚ)) {h : Equiv.Perm ℚ}
    (hh : h ∈ gammaTwo) (hhN : ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hcore : ⁅perCore 4, perCore 4⁆ ≤ N)
    (hnot : ∀ k : ℤ, h 0 ≠ k) : ∃ g ∈ N, 0 < g 0 ∧ g 0 < 1 := by
  have hhi : h⁻¹ ∈ gammaTwo := gammaTwo.inv_mem hh
  obtain ⟨x, hxdef⟩ : ∃ x : ℚ, h⁻¹ 0 = x := ⟨_, rfl⟩
  have hx0 : h x = 0 := by
    rw [← hxdef]
    exact perm_apply_inv_self h 0
  have hxnot : ∀ k : ℤ, x ≠ k := by
    intro k hk
    apply hnot (-k)
    have e := gammaTwo_add_int hh 0 k
    rw [zero_add, ← hk, hx0] at e
    push_cast
    linarith
  have hr0 : 0 < Int.fract x := by
    rcases lt_or_eq_of_le (Int.fract_nonneg x) with h' | h'
    · exact h'
    · exfalso
      apply hxnot ⌊x⌋
      have e := Int.floor_add_fract x
      rw [← h', add_zero] at e
      exact e.symm
  have hr1 := Int.fract_lt_one x
  have hxg : ∃ M, x ∈ Grid 6 M := by
    have h' := gammaTwo_apply_grid hhi zero_mem_grid_six
    rwa [hxdef] at h'
  have hrg := fract_grid hxg
  obtain ⟨y, hry, hy1, hyres, hyg⟩ := exists_resEq_mem_Ioo (m := 4) hrg hr1
  obtain ⟨a, haK, hax⟩ := exists_perCore_apply hrg hyg hyres hr0 hr1 (by linarith) hy1
  have hP0 : (perHom 4 a)⁻¹ 0 = 0 := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact_mod_cast (perHom_apply_intCast a 0).symm
  have hPx : perHom 4 a x = ⌊x⌋ + y := by
    have e := perHom_add_int 4 a (Int.fract x) ⌊x⌋
    rw [Int.fract_add_floor, hax] at e
    rw [e, add_comm]
  have hval : ⁅h, perHom 4 a⁆ 0 = h (⌊x⌋ + y) := by
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    rw [hP0, hxdef, hPx]
  have hmono := gammaTwo_strictMono hh
  have hflr : h (⌊x⌋ + Int.fract x) = 0 := by
    rw [Int.floor_add_fract]
    exact hx0
  have hlow : 0 < h (⌊x⌋ + y) := by
    have h' := hmono (show (⌊x⌋ : ℚ) + Int.fract x < ⌊x⌋ + y by linarith)
    rwa [hflr] at h'
  have hhigh : h (⌊x⌋ + y) < 1 := by
    have h1 : h ((⌊x⌋ + Int.fract x) + ((1 : ℤ) : ℚ)) =
        h (⌊x⌋ + Int.fract x) + ((1 : ℤ) : ℚ) := gammaTwo_add_int hh _ 1
    rw [hflr] at h1
    have h2 := hmono (show (⌊x⌋ : ℚ) + y < (⌊x⌋ + Int.fract x) + ((1 : ℤ) : ℚ) by
      push_cast
      linarith)
    rw [h1] at h2
    push_cast at h2
    linarith
  refine ⟨⁅h, perHom 4 a⁆, ?_, by rw [hval]; exact hlow, by rw [hval]; exact hhigh⟩
  rw [commutatorElement_def]
  exact N.mul_mem (hhN _ (hcore haK)) (N.inv_mem (hcore haK))

#audit_axioms GroupApproximation.HydeLodha.commutator_perCore_le_gammaTwo
#audit_axioms GroupApproximation.HydeLodha.not_translation_of_mem_gammaTwo
#audit_axioms GroupApproximation.HydeLodha.commutator_perCore_le_of_ne_bot
#audit_axioms GroupApproximation.HydeLodha.exists_perCore_apply
#audit_axioms GroupApproximation.HydeLodha.exists_mem_unit_of_not_int

end HydeLodha
end GroupApproximation
