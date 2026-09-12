import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationGermAt
import GroupApproximation.Meta.AxiomGuard

/-!
# Hyde–Lodha, Lemma 4.3, with explicit germs

"For each `a, b ∈ ℤ[1/η_n]`, `0 < b - a ≤ 1`, there exists `f ∈ Υ_{Q_n}([a, b])` such that
`a·f'_+ = b·f'_- = η_n`."  In the unit frame `0 < a < b < 1` (Lemma 4.6 reduces to it by
`exists_move_into_unit`):

* `exists_upsilon_qTwo_germs`: some `f ∈ Υ_{Q₂}([a, b])` is `t ↦ a + 6 (t - a)` on `[a, a + ε]` and
  `t ↦ b + 6 (t - b)` on `[b - ε, b]`.  The printed proof takes `f = [f₂, h]^{f₁⁻¹}`; here
  `f = ⁅P_a, x⁆ ⁅P_b, z⁆`, where `P_a`, `P_b` are the periodic germ elements `germAt`, `germAtR`,
  and `x`, `z ∈ F_6'` push `a` into the support of `P_a` and `b` into that of `P_b`, so the germs of
  the commutators at `a⁺` and `b⁻` are those of `P_a` and `P_b`;
* `exists_upsilon_gammaTwo_germLeft`: the one-sided element of `Υ_{Γ₂}([a, a + δ])` used in Lemma 4.5.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

theorem exists_perHom_mapsTo {u v u' v' : ℚ} (hu : ∃ M, u ∈ Grid 6 M) (hv : ∃ M, v ∈ Grid 6 M)
    (hu' : ∃ M, u' ∈ Grid 6 M) (hv' : ∃ M, v' ∈ Grid 6 M) (hru : ResEq 4 u' u)
    (hrv : ResEq 4 v' v) (h0u : 0 < u) (huv : u < v) (hv1 : v < 1) (h0u' : 0 < u')
    (huv' : u' < v') (hv1' : v' < 1) :
    ∃ p : ↥(compactF 4 1), perHom 4 p u = u' ∧ perHom 4 p v = v' := by
  obtain ⟨k, hk, hku, hkv⟩ := exists_compactCore_mapsTo (m := 4) hu hv hu' hv' hru hrv h0u huv
    hv1 h0u' huv' hv1'
  refine ⟨⟨k, compactCore_le hk⟩, ?_, ?_⟩
  · rw [perHom_apply_of_mem 4 _ h0u.le (by linarith)]
    exact hku
  · rw [perHom_apply_of_mem 4 _ (by linarith) hv1]
    exact hkv

theorem grid_add_zetaN {a : ℚ} (ha : ∃ M, a ∈ Grid 6 M) (N : ℕ) : ∃ M, a + zetaN N ∈ Grid 6 M := by
  obtain ⟨M, hM⟩ := ha
  exact ⟨max M N, grid_add (grid_mono (le_max_left M N) hM) (grid_mono (le_max_right M N)
    (zetaN_mem_grid N))⟩

theorem grid_sub_zetaN {b : ℚ} (hb : ∃ M, b ∈ Grid 6 M) (N : ℕ) : ∃ M, b - zetaN N ∈ Grid 6 M := by
  obtain ⟨M, hM⟩ := hb
  exact ⟨max M N, grid_sub (grid_mono (le_max_left M N) hM) (grid_mono (le_max_right M N)
    (zetaN_mem_grid N))⟩

/-- **The one-sided germ element** (for Lemma 4.5). -/
theorem exists_upsilon_gammaTwo_germLeft {a δ : ℚ} (ha : ∃ M, a ∈ Grid 6 M) (h0a : 0 ≤ a)
    (hδ : 0 < δ) (h1 : a + δ ≤ 1) :
    ∃ f ∈ upsilon gammaTwo a (a + δ), ∃ ε : ℚ, GermLeft 4 a 1 ε f := by
  obtain ⟨N, -, hN⟩ := exists_level (m := 4) 0 (δ := δ / 7) (by linarith)
  have hz := zetaN_le_of_sixInv_le hN
  have hmem := germAt_mem ha N h0a (by linarith)
  obtain ⟨hPΓ, hPs⟩ := mem_upsilon.mp (perHom_germAt_mem_upsilon hmem)
  refine ⟨perHom 4 ⟨germAt a N, hmem⟩, mem_upsilon.mpr ⟨hPΓ, hPs.mono
    (perIoo_mono le_rfl (by linarith))⟩, ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹, ?_⟩
  unfold GermLeft
  refine ⟨sixInv_pos N, fun t ht1 ht2 => ?_⟩
  rw [perHom_germAt_near hmem (by linarith) ht1 h0a ht2, zpow_one, six_cast]

/-- **Hyde–Lodha, Lemma 4.3**, in the unit frame. -/
theorem exists_upsilon_qTwo_germs {a b : ℚ} (ha : ∃ M, a ∈ Grid 6 M) (hb : ∃ M, b ∈ Grid 6 M)
    (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    ∃ f ∈ upsilon qTwo a b, ∃ ε : ℚ, GermLeft 4 a 1 ε f ∧ GermRight 4 b 1 ε f := by
  obtain ⟨N, -, hN⟩ := exists_level (m := 4) 0 (δ := (b - a) / 28) (by linarith)
  have hXpos := sixInv_pos N
  have hXz := sixInv_lt_zetaN N
  have hz := zetaN_le_of_sixInv_le hN
  -- the germ elements
  have hmemL := germAt_mem ha N h0a.le (by linarith)
  have hmemR := germAtR_mem hb N (by linarith) hb1.le
  obtain ⟨hPLΓ, hPLs⟩ := mem_upsilon.mp (perHom_germAt_mem_upsilon hmemL)
  obtain ⟨hPRΓ, hPRs⟩ := mem_upsilon.mp (perHom_germAtR_mem_upsilon hmemR)
  have hPLg : ∀ t, a ≤ t → t ≤ a + ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ →
      perHom 4 ⟨germAt a N, hmemL⟩ t = a + 6 * (t - a) :=
    fun t h1 h2 => perHom_germAt_near hmemL (by linarith) h1 h0a.le h2
  have hPRg : ∀ t, b - ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ ≤ t → t ≤ b →
      perHom 4 ⟨germAtR b N, hmemR⟩ t = b + 6 * (t - b) :=
    fun t h1 h2 => perHom_germAtR_near hmemR hb1 (by linarith) h1 h2
  generalize perHom 4 ⟨germAt a N, hmemL⟩ = PL at hPLΓ hPLs hPLg
  generalize perHom 4 ⟨germAtR b N, hmemR⟩ = PR at hPRΓ hPRs hPRg
  -- the pushing elements
  obtain ⟨y₁, hy₁a, hy₁z, hry₁, hy₁G⟩ := exists_resEq_mem_Ioo (m := 4) ha
    (show a < a + zetaN N by linarith)
  obtain ⟨y₂, hy₂z, hy₂m, hry₂, hy₂G⟩ := exists_resEq_mem_Ioo (m := 4) (grid_add_zetaN ha N)
    (show a + zetaN N < (a + b) / 2 by linarith)
  obtain ⟨p, hpa, hpz⟩ := exists_perHom_mapsTo ha (grid_add_zetaN ha N) hy₁G hy₂G hry₁ hry₂ h0a
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨w₁, hw₁m, hw₁z, hrw₁, hw₁G⟩ := exists_resEq_mem_Ioo (m := 4) (grid_sub_zetaN hb N)
    (show (a + b) / 2 < b - zetaN N by linarith)
  obtain ⟨w₂, hw₂z, hw₂b, hrw₂, hw₂G⟩ := exists_resEq_mem_Ioo (m := 4) hb
    (show b - zetaN N < b by linarith)
  obtain ⟨q, hqz, hqb⟩ := exists_perHom_mapsTo (grid_sub_zetaN hb N) hb hw₁G hw₂G hrw₁ hrw₂
    (by linarith) (by linarith) hb1 (by linarith) (by linarith) (by linarith)
  have hxΓ := perHom_mem_gammaTwo p
  have hzΓ := perHom_mem_gammaTwo q
  have hx0 : perHom 4 p 0 = 0 := by exact_mod_cast perHom_apply_intCast p 0
  have hz1 : perHom 4 q 1 = 1 := by exact_mod_cast perHom_apply_intCast q 1
  generalize perHom 4 p = x at hxΓ hx0 hpa hpz
  generalize perHom 4 q = z at hzΓ hz1 hqz hqb
  -- the left commutator
  have hfLQ : ⁅PL, x⁆ ∈ qTwo := Subgroup.commutator_mem_commutator hPLΓ hxΓ
  have hfLs : SupportedIn ⁅PL, x⁆ (perIoo a ((a + b) / 2)) :=
    supportedIn_commutator hPLs (perIoo_mono le_rfl (by linarith))
      ((image_perIoo_subset hxΓ a (a + zetaN N)).trans
        (by rw [hpa, hpz]; exact perIoo_mono hy₁a.le hy₂m.le))
  have hfLg : ∀ t, a ≤ t → t ≤ a + ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ → t ≤ y₁ →
      ⁅PL, x⁆ t = a + 6 * (t - a) := by
    intro t h1 h2 h3
    have hmono := gammaTwo_strictMono hxΓ
    have hs1 : x⁻¹ t ≤ a := by
      by_contra hc
      have h' := hmono (not_le.mp hc)
      rw [perm_apply_inv_self, hpa] at h'
      linarith
    have hs0 : 0 < x⁻¹ t := by
      by_contra hc
      have h' := hmono.monotone (not_lt.mp hc)
      rw [perm_apply_inv_self, hx0] at h'
      linarith
    have hnot : x⁻¹ t ∉ perIoo a (a + zetaN N) := by
      rintro ⟨k, hk1, hk2⟩
      rcases le_or_gt k 0 with hk | hk
      · have hk' : (k : ℚ) ≤ 0 := by exact_mod_cast hk
        linarith
      · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
        linarith
    rw [commutator_apply_of_inv_not_mem hPLs hnot, hPLg t h1 h2]
  -- the right commutator
  have hfRQ : ⁅PR, z⁆ ∈ qTwo := Subgroup.commutator_mem_commutator hPRΓ hzΓ
  have hfRs : SupportedIn ⁅PR, z⁆ (perIoo ((a + b) / 2) b) :=
    supportedIn_commutator hPRs (perIoo_mono (by linarith) le_rfl)
      ((image_perIoo_subset hzΓ (b - zetaN N) b).trans
        (by rw [hqz, hqb]; exact perIoo_mono hw₁m.le hw₂b.le))
  have hfRg : ∀ t, b - ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ ≤ t → t ≤ b → w₂ ≤ t →
      ⁅PR, z⁆ t = b + 6 * (t - b) := by
    intro t h1 h2 h3
    have hmono := gammaTwo_strictMono hzΓ
    have hs1 : b ≤ z⁻¹ t := by
      by_contra hc
      have h' := hmono (not_le.mp hc)
      rw [perm_apply_inv_self, hqb] at h'
      linarith
    have hs2 : z⁻¹ t < 1 := by
      by_contra hc
      have h' := hmono.monotone (not_lt.mp hc)
      rw [perm_apply_inv_self, hz1] at h'
      linarith
    have hnot : z⁻¹ t ∉ perIoo (b - zetaN N) b := by
      rintro ⟨k, hk1, hk2⟩
      rcases le_or_gt 0 k with hk | hk
      · have hk' : (0 : ℚ) ≤ k := by exact_mod_cast hk
        linarith
      · have hk' : (k : ℚ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        linarith
    rw [commutator_apply_of_inv_not_mem hPRs hnot, hPRg t h1 h2]
  -- the product
  have hfQ : ⁅PL, x⁆ * ⁅PR, z⁆ ∈ qTwo := qTwo.mul_mem hfLQ hfRQ
  have hfs : SupportedIn (⁅PL, x⁆ * ⁅PR, z⁆) (perIoo a b) :=
    (hfLs.mul hfRs).mono (Set.union_subset (perIoo_mono le_rfl (by linarith))
      (perIoo_mono (by linarith) le_rfl))
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℚ,
      ε = min (min ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ (y₁ - a)) (min (b - w₂) ((b - a) / 12)) :=
    ⟨_, rfl⟩
  have hε1 : ε ≤ ((((4 : ℕ) : ℚ) + 2) ^ N)⁻¹ := by
    rw [hεdef]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hε2 : ε ≤ y₁ - a := by
    rw [hεdef]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hε3 : ε ≤ b - w₂ := by
    rw [hεdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε4 : ε ≤ (b - a) / 12 := by
    rw [hεdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min hXpos (by linarith)) (lt_min (by linarith) (by linarith))
  refine ⟨⁅PL, x⁆ * ⁅PR, z⁆, mem_upsilon.mpr ⟨hfQ, hfs⟩, ε, ?_, ?_⟩
  · unfold GermLeft
    refine ⟨hεpos, fun t h1 h2 => ?_⟩
    have hnotR : t ∉ perIoo ((a + b) / 2) b := by
      rintro ⟨k, hk1, hk2⟩
      rcases le_or_gt k 0 with hk | hk
      · have hk' : (k : ℚ) ≤ 0 := by exact_mod_cast hk
        linarith
      · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
        linarith
    rw [Equiv.Perm.mul_apply, hfRs t hnotR, hfLg t h1 (by linarith) (by linarith), zpow_one,
      six_cast]
  · unfold GermRight
    refine ⟨hεpos, fun t h1 h2 => ?_⟩
    have hnotL : b + 6 * (t - b) ∉ perIoo a ((a + b) / 2) := by
      rintro ⟨k, hk1, hk2⟩
      rcases lt_trichotomy k 0 with hk | hk | hk
      · have hk' : (k : ℚ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        linarith
      · rw [hk, Int.cast_zero, add_zero] at hk2
        linarith
      · have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
        linarith
    rw [Equiv.Perm.mul_apply, hfRg t (by linarith) h2 (by linarith), hfLs _ hnotL, zpow_one,
      six_cast]

#audit_axioms GroupApproximation.HydeLodha.exists_upsilon_gammaTwo_germLeft
#audit_axioms GroupApproximation.HydeLodha.exists_upsilon_qTwo_germs

end HydeLodha
end GroupApproximation
