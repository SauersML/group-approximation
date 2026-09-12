import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationMove
import GroupApproximation.GroupTheory.HigmanThompson.RstabGerms
import GroupApproximation.Meta.AxiomGuard

/-!
# Germ elements at interior grid points

The explicit elements behind Hyde–Lodha's Lemma 4.3, in the unit frame `0 ≤ a < b ≤ 1`.  They are
`HigmanThompson.germLeft` / `germRight` moved by a translation:

* `germAt a N`: the identity outside `(a, a + ζ_N)`, `t ↦ a + 6 (t - a)` on `[a, a + 6^{-N}]`
  (`germAt_near`), where `ζ_N = 7 / 6^N` (`zetaN`);
* `germAtR b N`: the identity outside `(b - ζ_N, b)`, `t ↦ b + 6 (t - b)` on `[b - 6^{-N}, b]`;
* both lie in `F_{6,1}` (`germAt_mem`, `germAtR_mem`), and their periodic extensions lie in
  `Υ_{Γ₂}` of the corresponding periodic interval.

Two facts about commutators used for Lemma 4.3: `supportedIn_commutator` and
`commutator_apply_of_inv_not_mem` (the germ of `⁅P, x⁆` is the germ of `P` where `x⁻¹` moves the
point off the support of `P`).
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

/-! ## Periodic intervals and commutators -/

theorem perIoo_mono {a b a₂ b₂ : ℚ} (ha : a ≤ a₂) (hb : b₂ ≤ b) : perIoo a₂ b₂ ⊆ perIoo a b := by
  rintro t ⟨k, h1, h2⟩
  exact ⟨k, by linarith, by linarith⟩

theorem perSet_Ioo_subset (u v : ℚ) : perSet (Set.Ioo u v) ⊆ perIoo u v := by
  intro t ht
  have ht' : Int.fract t ∈ Set.Ioo u v := ht
  have e : t + ((-⌊t⌋ : ℤ) : ℚ) = Int.fract t := by
    rw [← Int.self_sub_floor]
    push_cast
    ring
  exact ⟨-⌊t⌋, by rw [e]; exact ht'.1, by rw [e]; exact ht'.2⟩

theorem supportedIn_commutator {P x : Equiv.Perm ℚ} {U V : Set ℚ} (hP : SupportedIn P U)
    (hU : U ⊆ V) (hxU : x '' U ⊆ V) : SupportedIn ⁅P, x⁆ V := by
  have e : ⁅P, x⁆ = P * (x * P⁻¹ * x⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (hP.mul (hP.inv.conj x)).mono (Set.union_subset hU hxU)

theorem commutator_apply_of_inv_not_mem {P x : Equiv.Perm ℚ} {U : Set ℚ} (hP : SupportedIn P U)
    {t : ℚ} (ht : x⁻¹ t ∉ U) : ⁅P, x⁆ t = P t := by
  rw [commutatorElement_def]
  simp only [Equiv.Perm.mul_apply]
  rw [hP.inv _ ht, perm_apply_inv_self]

/-! ## The constants -/

/-- `ζ_N = 7 / 6^N`, spelled as in the hypotheses of `germLeft`. -/
def zetaN (N : ℕ) : ℚ := (((4 : ℕ) : ℚ) + 3) * ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹

theorem six_cast : (((4 : ℕ) : ℚ) + 2) = 6 := by norm_num

theorem sixInv_pos (N : ℕ) : (0 : ℚ) < ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ :=
  inv_pos.mpr (pow_pos (by norm_num) N)

theorem sixInv_lt_zetaN (N : ℕ) : ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ < zetaN N := by
  have h := sixInv_pos N
  have e : (((4 : ℕ) : ℚ) + 3) = 7 := by norm_num
  rw [zetaN, e]
  linarith

theorem zetaN_le_of_sixInv_le {N : ℕ} {δ : ℚ} (h : ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ ≤ δ) :
    zetaN N ≤ 7 * δ := by
  have e : (((4 : ℕ) : ℚ) + 3) = 7 := by norm_num
  rw [zetaN, e]
  linarith

theorem zetaN_mem_grid (N : ℕ) : zetaN N ∈ Grid (4 + 2) N := by
  refine ⟨7, ?_⟩
  have hc : ((4 + 2 : ℕ) : ℚ) = ((4 : ℕ) : ℚ) + 2 := by push_cast; ring
  have h6 : (((4 : ℕ) : ℚ) + 2) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  rw [zetaN, hc, inv_mul_cancel_right₀ h6]
  norm_num

/-! ## `germAt` -/

/-- `germLeft` moved to `a`. -/
noncomputable def germAt (a : ℚ) (N : ℕ) : Equiv.Perm ℚ :=
  transPerm a * germLeft 4 N (zetaN N) * (transPerm a)⁻¹

theorem germAt_apply (a : ℚ) (N : ℕ) (t : ℚ) :
    germAt a N t = germLeft 4 N (zetaN N) (t - a) + a := rfl

theorem germAt_supportedIn (a : ℚ) (N : ℕ) : SupportedIn (germAt a N) (Set.Ioo a (a + zetaN N)) := by
  intro t ht
  rw [germAt_apply]
  rcases le_or_gt t a with h | h
  · rw [germLeft_of_nonpos (m := 4) (ζ := zetaN N) (u := t - a) N le_rfl (by linarith)]
    ring
  · have h' : a + zetaN N ≤ t := by
      by_contra hc
      exact ht ⟨h, not_le.mp hc⟩
    rw [germLeft_of_ge (m := 4) (ζ := zetaN N) (u := t - a) N le_rfl (by linarith)]
    ring

theorem germAt_near {a : ℚ} (N : ℕ) {t : ℚ} (h1 : a ≤ t)
    (h2 : t ≤ a + ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹) : germAt a N t = a + 6 * (t - a) := by
  rw [germAt_apply, germLeft_near (m := 4) (ζ := zetaN N) (u := t - a) N le_rfl (by linarith)
    (by linarith), six_cast]
  ring

theorem germAt_mem {a : ℚ} (ha : ∃ M, a ∈ Grid 6 M) (N : ℕ) (h0 : 0 ≤ a)
    (h1 : a + zetaN N ≤ 1) : germAt a N ∈ compactF 4 1 := by
  obtain ⟨M, hM⟩ := ha
  have hz := zetaN_mem_grid N
  show germAt a N ∈ PLGroup (4 + 2) (powSlopes 4) ∧ (∀ t : ℚ, t ≤ 0 → germAt a N t = t) ∧
    ∀ t : ℚ, ((1 : ℕ) : ℚ) ≤ t → germAt a N t = t
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
  · exact (PLGroup (4 + 2) (powSlopes 4)).mul_mem
      ((PLGroup (4 + 2) (powSlopes 4)).mul_mem (transPerm_mem (m := 4) hM)
        (germLeft_mem (m := 4) N hz))
      ((PLGroup (4 + 2) (powSlopes 4)).inv_mem (transPerm_mem (m := 4) hM))
  · rw [germAt_apply, germLeft_of_nonpos (m := 4) (ζ := zetaN N) (u := t - a) N le_rfl
      (by linarith)]
    ring
  · have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
    rw [germAt_apply, germLeft_of_ge (m := 4) (ζ := zetaN N) (u := t - a) N le_rfl (by linarith)]
    ring

/-! ## `germAtR` -/

/-- `germRight` moved to `b`. -/
noncomputable def germAtR (b : ℚ) (N : ℕ) : Equiv.Perm ℚ :=
  transPerm (b - 1) * germRight 4 N (zetaN N) * (transPerm (b - 1))⁻¹

theorem germAtR_apply (b : ℚ) (N : ℕ) (t : ℚ) :
    germAtR b N t = germRight 4 N (zetaN N) (t - (b - 1)) + (b - 1) := rfl

theorem germAtR_supportedIn (b : ℚ) (N : ℕ) :
    SupportedIn (germAtR b N) (Set.Ioo (b - zetaN N) b) := by
  intro t ht
  rw [germAtR_apply]
  rcases le_or_gt t (b - zetaN N) with h | h
  · rw [germRight_of_le (m := 4) (ζ := zetaN N) (u := t - (b - 1)) N le_rfl (by linarith)]
    ring
  · have h' : b ≤ t := by
      by_contra hc
      exact ht ⟨h, not_le.mp hc⟩
    rw [germRight_of_ge (m := 4) (ζ := zetaN N) (u := t - (b - 1)) N le_rfl (by linarith)]
    ring

theorem germAtR_near {b : ℚ} (N : ℕ) {t : ℚ} (h1 : b - ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ ≤ t)
    (h2 : t ≤ b) : germAtR b N t = b + 6 * (t - b) := by
  rw [germAtR_apply, germRight_near (m := 4) (ζ := zetaN N) (u := t - (b - 1)) N le_rfl
    (by linarith) (by linarith), six_cast]
  ring

theorem germAtR_mem {b : ℚ} (hb : ∃ M, b ∈ Grid 6 M) (N : ℕ) (h0 : zetaN N ≤ b) (h1 : b ≤ 1) :
    germAtR b N ∈ compactF 4 1 := by
  obtain ⟨M, hM⟩ := hb
  have hz := zetaN_mem_grid N
  have hb1 : b - 1 ∈ Grid (4 + 2) M := grid_sub hM (one_mem_grid_six M)
  show germAtR b N ∈ PLGroup (4 + 2) (powSlopes 4) ∧ (∀ t : ℚ, t ≤ 0 → germAtR b N t = t) ∧
    ∀ t : ℚ, ((1 : ℕ) : ℚ) ≤ t → germAtR b N t = t
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
  · exact (PLGroup (4 + 2) (powSlopes 4)).mul_mem
      ((PLGroup (4 + 2) (powSlopes 4)).mul_mem (transPerm_mem (m := 4) hb1)
        (germRight_mem (m := 4) N hz))
      ((PLGroup (4 + 2) (powSlopes 4)).inv_mem (transPerm_mem (m := 4) hb1))
  · rw [germAtR_apply, germRight_of_le (m := 4) (ζ := zetaN N) (u := t - (b - 1)) N le_rfl
      (by linarith)]
    ring
  · have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
    rw [germAtR_apply, germRight_of_ge (m := 4) (ζ := zetaN N) (u := t - (b - 1)) N le_rfl
      (by linarith)]
    ring

/-! ## Periodic extensions -/

theorem perHom_germAt_mem_upsilon {a : ℚ} {N : ℕ} (hmem : germAt a N ∈ compactF 4 1) :
    perHom 4 ⟨germAt a N, hmem⟩ ∈ upsilon gammaTwo a (a + zetaN N) :=
  mem_upsilon.mpr ⟨perHom_mem_gammaTwo _,
    (supportedIn_perHom 4 (f := ⟨germAt a N, hmem⟩) (germAt_supportedIn a N)).mono
      (perSet_Ioo_subset _ _)⟩

theorem perHom_germAtR_mem_upsilon {b : ℚ} {N : ℕ} (hmem : germAtR b N ∈ compactF 4 1) :
    perHom 4 ⟨germAtR b N, hmem⟩ ∈ upsilon gammaTwo (b - zetaN N) b :=
  mem_upsilon.mpr ⟨perHom_mem_gammaTwo _,
    (supportedIn_perHom 4 (f := ⟨germAtR b N, hmem⟩) (germAtR_supportedIn b N)).mono
      (perSet_Ioo_subset _ _)⟩

theorem perHom_germAt_near {a : ℚ} {N : ℕ} (hmem : germAt a N ∈ compactF 4 1)
    (h1a : a + zetaN N ≤ 1) {t : ℚ} (h1 : a ≤ t) (h0 : 0 ≤ a)
    (h2 : t ≤ a + ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹) :
    perHom 4 ⟨germAt a N, hmem⟩ t = a + 6 * (t - a) := by
  have hX := sixInv_lt_zetaN N
  rw [perHom_apply_of_mem 4 _ (by linarith) (by linarith)]
  exact germAt_near N h1 h2

theorem perHom_germAtR_near {b : ℚ} {N : ℕ} (hmem : germAtR b N ∈ compactF 4 1) (hb1 : b < 1)
    (hzb : zetaN N ≤ b) {t : ℚ} (h1 : b - ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ ≤ t) (h2 : t ≤ b) :
    perHom 4 ⟨germAtR b N, hmem⟩ t = b + 6 * (t - b) := by
  have hX := sixInv_lt_zetaN N
  rw [perHom_apply_of_mem 4 _ (by linarith) (by linarith)]
  exact germAtR_near N h1 h2

#audit_axioms GroupApproximation.HydeLodha.supportedIn_commutator
#audit_axioms GroupApproximation.HydeLodha.commutator_apply_of_inv_not_mem
#audit_axioms GroupApproximation.HydeLodha.germAt_mem
#audit_axioms GroupApproximation.HydeLodha.germAtR_mem
#audit_axioms GroupApproximation.HydeLodha.perHom_germAt_near
#audit_axioms GroupApproximation.HydeLodha.perHom_germAtR_near

end HydeLodha
end GroupApproximation
