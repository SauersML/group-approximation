import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationRestrict
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting `Γ_K` at the points of `K`

Hyde–Lodha, proof of Proposition 4.7: "suppose that `max(K) < min(K) + 1`.  Thus, this provides
`|K|` (left closed, right open) intervals `L_1, …, L_{|K|}` such that `L = ⋃ L_i` is an interval
whose closure has length `1` and `L + ℤ` partitions `ℝ`.  Let `R = ∏ Rstab_{Γ_n}(L_j)` and
`R_1 = ∏ Rstab_Γ(L_j)`.  From our hypothesis, it follows that `R' ⊆ R_1 ⊆ Γ_K ⊆ R`."

We add the points of `K` one at a time, largest first.  Writing `X_Γ(c, e, S) = Υ_Γ([c, e]) ∩ Γ_S`,
for `c < s < d < e ≤ c + 1`:

* `upsilon_inf_stabK_le_insert`, `upsilon_le_insert`:
  `X_Γ(c, d, s) ⊔ Υ_Γ([d, e]) ≤ X_Γ(c, e, s ∪ {d})`;
* `commute_upsilon_inf_stabK`, `upsilon_inf_stabK_inf_upsilon_eq_bot`: the two factors commute and
  meet trivially (`disjoint_perIoo`);
* `upsilon_inf_stabK_insert_gammaTwo`: `X_{Γ₂}(c, e, s ∪ {d}) = X_{Γ₂}(c, d, s) ⊔ Υ_{Γ₂}([d, e])`,
  by `exists_upsilon_split`;
* `commutator_upsilon_inf_stabK_le`, `commutator_upsilon_le`: for `Q₂ ≤ Γ`,
  `X_{Γ₂}(c, d, s)' ≤ X_Γ(c, d, s)` and `Υ_{Γ₂}([d, e])' ≤ Υ_Γ([d, e])`.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

theorem mem_perIoo_of_mem_Ioo {c d t : ℚ} (hct : c < t) (htd : t < d) : t ∈ perIoo c d :=
  ⟨0, by simpa using hct, by simpa using htd⟩

theorem left_not_mem_perIoo {c d : ℚ} (hdc : d ≤ c + 1) : c ∉ perIoo c d := by
  rintro ⟨k, h1, h2⟩
  rcases lt_or_ge k 1 with hk | hk
  · have hk' : (k : ℚ) ≤ 0 := by exact_mod_cast (show k ≤ 0 by omega)
    linarith
  · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith

theorem right_not_mem_perIoo {c d : ℚ} (hdc : d ≤ c + 1) : d ∉ perIoo c d := by
  rintro ⟨k, h1, h2⟩
  rcases lt_or_ge k 0 with hk | hk
  · have hk' : (k : ℚ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    linarith
  · have hk' : (0 : ℚ) ≤ k := by exact_mod_cast hk
    linarith

theorem disjoint_perIoo {c d e : ℚ} (hec : e ≤ c + 1) : Disjoint (perIoo c d) (perIoo d e) := by
  rw [Set.disjoint_left]
  rintro t ⟨j, hj1, hj2⟩ ⟨i, hi1, hi2⟩
  rcases lt_trichotomy i j with h | rfl | h
  · have h' : (i : ℚ) ≤ j - 1 := by exact_mod_cast (show i ≤ j - 1 by omega)
    linarith
  · linarith
  · have h' : (j : ℚ) ≤ i - 1 := by exact_mod_cast (show j ≤ i - 1 by omega)
    linarith

/-! ## The two factors -/

theorem upsilon_inf_stabK_le_insert {Γ : Subgroup (Equiv.Perm ℚ)} {c d e : ℚ} {s : Finset ℚ}
    (hde : d ≤ e) (hdc : d ≤ c + 1) :
    upsilon Γ c d ⊓ stabK Γ ↑s ≤ upsilon Γ c e ⊓ stabK Γ ↑(insert d s) := by
  intro f hf
  obtain ⟨hfU, hfS⟩ := Subgroup.mem_inf.mp hf
  obtain ⟨hfΓ, hfs⟩ := mem_upsilon.mp hfU
  refine Subgroup.mem_inf.mpr ⟨mem_upsilon.mpr ⟨hfΓ, hfs.mono ?_⟩,
    mem_stabK.mpr ⟨hfΓ, fun k hk => ?_⟩⟩
  · rintro t ⟨j, h1, h2⟩
    exact ⟨j, h1, by linarith⟩
  · rw [Finset.coe_insert, Set.mem_insert_iff] at hk
    rcases hk with rfl | hk
    · exact hfs _ (right_not_mem_perIoo hdc)
    · exact (mem_stabK.mp hfS).2 k hk

theorem upsilon_le_insert {Γ : Subgroup (Equiv.Perm ℚ)} {c d e : ℚ} {s : Finset ℚ}
    (hcd : c ≤ d) (hec : e ≤ c + 1) (hs : ∀ k ∈ s, c < k ∧ k < d) :
    upsilon Γ d e ≤ upsilon Γ c e ⊓ stabK Γ ↑(insert d s) := by
  intro f hf
  obtain ⟨hfΓ, hfs⟩ := mem_upsilon.mp hf
  refine Subgroup.mem_inf.mpr ⟨mem_upsilon.mpr ⟨hfΓ, hfs.mono ?_⟩,
    mem_stabK.mpr ⟨hfΓ, fun k hk => ?_⟩⟩
  · rintro t ⟨j, h1, h2⟩
    exact ⟨j, by linarith, h2⟩
  · rw [Finset.coe_insert, Set.mem_insert_iff] at hk
    rcases hk with rfl | hk
    · exact hfs _ (left_not_mem_perIoo (by linarith))
    · obtain ⟨hck, hkd⟩ := hs k (Finset.mem_coe.mp hk)
      exact hfs _ (Set.disjoint_left.mp (disjoint_perIoo hec) (mem_perIoo_of_mem_Ioo hck hkd))

theorem commute_upsilon_inf_stabK {Γ Γ' : Subgroup (Equiv.Perm ℚ)} {c d e : ℚ} (S : Set ℚ)
    (hec : e ≤ c + 1) : ∀ a ∈ upsilon Γ c d ⊓ stabK Γ S, ∀ b ∈ upsilon Γ' d e, Commute a b :=
  fun _ ha _ hb => commute_of_supportedIn (mem_upsilon.mp (Subgroup.mem_inf.mp ha).1).2
    (mem_upsilon.mp hb).2 (disjoint_perIoo hec)

theorem upsilon_inf_stabK_inf_upsilon_eq_bot {Γ Γ' : Subgroup (Equiv.Perm ℚ)} {c d e : ℚ}
    (S : Set ℚ) (hec : e ≤ c + 1) : upsilon Γ c d ⊓ stabK Γ S ⊓ upsilon Γ' d e = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨hf₁, hf₂⟩ := Subgroup.mem_inf.mp hf
  have hs₁ := (mem_upsilon.mp (Subgroup.mem_inf.mp hf₁).1).2
  have hs₂ := (mem_upsilon.mp hf₂).2
  rw [Subgroup.mem_bot]
  ext t
  by_cases ht : t ∈ perIoo c d
  · exact hs₂ t (Set.disjoint_left.mp (disjoint_perIoo hec) ht)
  · exact hs₁ t ht

theorem upsilon_inf_stabK_mono {Γ Γ' : Subgroup (Equiv.Perm ℚ)} (hΓ : Γ ≤ Γ') (c e : ℚ)
    (S : Set ℚ) : upsilon Γ c e ⊓ stabK Γ S ≤ upsilon Γ' c e ⊓ stabK Γ' S := by
  intro f hf
  obtain ⟨hU, hS⟩ := Subgroup.mem_inf.mp hf
  exact Subgroup.mem_inf.mpr ⟨mem_upsilon.mpr ⟨hΓ (mem_upsilon.mp hU).1, (mem_upsilon.mp hU).2⟩,
    mem_stabK.mpr ⟨hΓ (mem_stabK.mp hS).1, (mem_stabK.mp hS).2⟩⟩

theorem upsilon_inf_stabK_empty (Γ : Subgroup (Equiv.Perm ℚ)) (c e : ℚ) :
    upsilon Γ c e ⊓ stabK Γ ↑(∅ : Finset ℚ) = upsilon Γ c e :=
  inf_eq_left.mpr fun _ hf => mem_stabK.mpr ⟨(mem_upsilon.mp hf).1, fun k hk => by simp at hk⟩

/-! ## `Γ_K ⊆ R` for `Γ₂` -/

/-- **`X_{Γ₂}(c, e, s ∪ {d}) = X_{Γ₂}(c, d, s) ⊔ Υ_{Γ₂}([d, e])`.** -/
theorem upsilon_inf_stabK_insert_gammaTwo {c d e : ℚ} {s : Finset ℚ} (hc : ∃ M, c ∈ Grid 6 M)
    (hd : ∃ M, d ∈ Grid 6 M) (hcd : c < d) (hde : d < e) (hec : e ≤ c + 1)
    (hs : ∀ k ∈ s, c < k ∧ k < d) :
    upsilon gammaTwo c e ⊓ stabK gammaTwo ↑(insert d s) =
      upsilon gammaTwo c d ⊓ stabK gammaTwo ↑s ⊔ upsilon gammaTwo d e := by
  apply le_antisymm
  · intro f hf
    obtain ⟨hfU, hfS⟩ := Subgroup.mem_inf.mp hf
    obtain ⟨hfΓ, hfs⟩ := mem_upsilon.mp hfU
    have hfix := (mem_stabK.mp hfS).2
    have hfc : f c = c := hfs c (left_not_mem_perIoo hec)
    have hfd : f d = d := hfix d (Finset.mem_coe.mpr (Finset.mem_insert_self d s))
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl, hagree⟩ := exists_upsilon_split hfΓ hfs hfc hfd hc hd
    refine Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hf₁,
      mem_stabK.mpr ⟨(mem_upsilon.mp hf₁).1, fun k hk => ?_⟩⟩) hf₂
    obtain ⟨hck, hkd⟩ := hs k (Finset.mem_coe.mp hk)
    rw [hagree k hck.le hkd.le]
    exact hfix k (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hk)))
  · exact sup_le (upsilon_inf_stabK_le_insert hde.le (by linarith))
      (upsilon_le_insert hcd.le hec hs)

/-! ## `R' ⊆ R_1` -/

theorem commutator_upsilon_inf_stabK_le {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (c d : ℚ)
    (S : Set ℚ) :
    ⁅upsilon gammaTwo c d ⊓ stabK gammaTwo S, upsilon gammaTwo c d ⊓ stabK gammaTwo S⁆ ≤
      upsilon Γ c d ⊓ stabK Γ S := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  have hmem : ⁅g₁, g₂⁆ ∈ upsilon gammaTwo c d ⊓ stabK gammaTwo S := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hQ' : ⁅g₁, g₂⁆ ∈ Γ := hQ (Subgroup.commutator_mem_commutator
    (mem_upsilon.mp (Subgroup.mem_inf.mp h₁).1).1 (mem_upsilon.mp (Subgroup.mem_inf.mp h₂).1).1)
  obtain ⟨hU, hS⟩ := Subgroup.mem_inf.mp hmem
  exact Subgroup.mem_inf.mpr ⟨mem_upsilon.mpr ⟨hQ', (mem_upsilon.mp hU).2⟩,
    mem_stabK.mpr ⟨hQ', (mem_stabK.mp hS).2⟩⟩

theorem commutator_upsilon_le {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (a b : ℚ) :
    ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆ ≤ upsilon Γ a b := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  have hmem : ⁅g₁, g₂⁆ ∈ upsilon gammaTwo a b := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  exact mem_upsilon.mpr ⟨hQ (Subgroup.commutator_mem_commutator (mem_upsilon.mp h₁).1
    (mem_upsilon.mp h₂).1), (mem_upsilon.mp hmem).2⟩

#audit_axioms GroupApproximation.HydeLodha.disjoint_perIoo
#audit_axioms GroupApproximation.HydeLodha.upsilon_inf_stabK_inf_upsilon_eq_bot
#audit_axioms GroupApproximation.HydeLodha.upsilon_inf_stabK_insert_gammaTwo
#audit_axioms GroupApproximation.HydeLodha.commutator_upsilon_inf_stabK_le

end HydeLodha
end GroupApproximation
