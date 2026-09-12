import GroupApproximation.GroupTheory.HigmanThompson.RstabIso
import GroupApproximation.GroupTheory.HigmanThompson.Orbits
import GroupApproximation.Meta.AxiomGuard

/-!
# Germs at the endpoints of `Rstab([c, d])`, and Hyde–Lodha's Lemma 4.4

Hyde–Lodha, Lemma 4.4: "Consider the standard action of `F_n` on `[0,1]`.  Let `I, J ⊂ (0,1)` be
closed intervals with endpoints in `ℤ[1/n]` such that `J ⊂ Int(I)`.  Then
`Rstab_{F_n}(I)' ∩ Rstab^c_{F_n}(J) = Rstab_{F_n}(J)'`", where `Rstab^c(J)` consists of the elements of
`Rstab(J)` with slope `1` at both endpoints of `J`.

For a piecewise linear element of `Rstab(J)` fixing the endpoints, slope `1` at an endpoint is the same
as being the identity near it; `rstabc m c d` records the latter.

* `exists_germLeft`, `exists_germRight`: an element of `rstab m c d` is `t ↦ c + n^i (t - c)` just
  right of `c` and `t ↦ d + n^j (t - d)` just left of `d`.
* `GermLeft.mul`, `GermLeft.inv` (and right): germ exponents add, so commutators have exponent `0`
  (`commutator_le_rstabc`).
* `rstab_commutator_inter_rstabc`: Lemma 4.4.  An element `g` of the left side is supported in some
  `[a₁, b₁] ⊂ Int(J)`; two moves give `h` fixing `[a₁, b₁]` and pushing `I` into `J`, so
  `g = h g h⁻¹ ∈ Rstab(h I)' ≤ Rstab(J)'`.
-/

namespace GroupApproximation
namespace HigmanThompson

open scoped commutatorElement
open HydeLodha

variable {m : ℕ}

/-! ## Germs -/

/-- `f` is `t ↦ c + n^i (t - c)` on `[c, c + ε]`. -/
def GermLeft (m : ℕ) (c : ℚ) (i : ℤ) (ε : ℚ) (f : Equiv.Perm ℚ) : Prop :=
  0 < ε ∧ ∀ t : ℚ, c ≤ t → t ≤ c + ε → f t = c + ((m : ℚ) + 2) ^ i * (t - c)

/-- `f` is `t ↦ d + n^j (t - d)` on `[d - ε, d]`. -/
def GermRight (m : ℕ) (d : ℚ) (j : ℤ) (ε : ℚ) (f : Equiv.Perm ℚ) : Prop :=
  0 < ε ∧ ∀ t : ℚ, d - ε ≤ t → t ≤ d → f t = d + ((m : ℚ) + 2) ^ j * (t - d)

section GermAlgebra

variable {c d : ℚ} {i j : ℤ} {ε ε' : ℚ} {f g : Equiv.Perm ℚ}

theorem GermLeft.mul (hf : GermLeft m c i ε f) (hg : GermLeft m c j ε' g) :
    GermLeft m c (i + j) (min ε' (ε * ((m : ℚ) + 2) ^ (-j))) (f * g) := by
  obtain ⟨hε, hf⟩ := hf
  obtain ⟨hε', hg⟩ := hg
  have hpj : (0 : ℚ) < ((m : ℚ) + 2) ^ j := zpow_pos mTwo_pos j
  have hpj' : (0 : ℚ) < ((m : ℚ) + 2) ^ (-j) := zpow_pos mTwo_pos (-j)
  have hjj : ((m : ℚ) + 2) ^ j * ((m : ℚ) + 2) ^ (-j) = 1 := by
    rw [← zpow_add₀ mTwo_pos.ne', add_neg_cancel, zpow_zero]
  refine ⟨lt_min hε' (mul_pos hε hpj'), fun t ht1 ht2 => ?_⟩
  have h1 := min_le_left ε' (ε * ((m : ℚ) + 2) ^ (-j))
  have h2 := min_le_right ε' (ε * ((m : ℚ) + 2) ^ (-j))
  rw [Equiv.Perm.mul_apply, hg t ht1 (by linarith)]
  have hlo : c ≤ c + ((m : ℚ) + 2) ^ j * (t - c) := by nlinarith
  have hhi : c + ((m : ℚ) + 2) ^ j * (t - c) ≤ c + ε := by
    have h3 : t - c ≤ ε * ((m : ℚ) + 2) ^ (-j) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hpj.le
    have e : ((m : ℚ) + 2) ^ j * (ε * ((m : ℚ) + 2) ^ (-j)) = ε := by
      linear_combination ε * hjj
    linarith
  rw [hf _ hlo hhi, zpow_add₀ mTwo_pos.ne']
  ring

theorem GermLeft.inv (hf : GermLeft m c i ε f) :
    GermLeft m c (-i) (ε * ((m : ℚ) + 2) ^ i) f⁻¹ := by
  obtain ⟨hε, hf⟩ := hf
  have hpi : (0 : ℚ) < ((m : ℚ) + 2) ^ i := zpow_pos mTwo_pos i
  have hii : ((m : ℚ) + 2) ^ i * ((m : ℚ) + 2) ^ (-i) = 1 := by
    rw [← zpow_add₀ mTwo_pos.ne', add_neg_cancel, zpow_zero]
  refine ⟨mul_pos hε hpi, fun t ht1 ht2 => ?_⟩
  apply perm_inv_eq_of_apply_eq
  have hpi' : (0 : ℚ) < ((m : ℚ) + 2) ^ (-i) := zpow_pos mTwo_pos (-i)
  have hlo : c ≤ c + ((m : ℚ) + 2) ^ (-i) * (t - c) := by nlinarith
  have hhi : c + ((m : ℚ) + 2) ^ (-i) * (t - c) ≤ c + ε := by
    have h3 : t - c ≤ ε * ((m : ℚ) + 2) ^ i := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hpi'.le
    have e : ((m : ℚ) + 2) ^ (-i) * (ε * ((m : ℚ) + 2) ^ i) = ε := by
      linear_combination ε * hii
    linarith
  rw [hf _ hlo hhi]
  linear_combination (t - c) * hii

theorem GermRight.mul (hf : GermRight m d i ε f) (hg : GermRight m d j ε' g) :
    GermRight m d (i + j) (min ε' (ε * ((m : ℚ) + 2) ^ (-j))) (f * g) := by
  obtain ⟨hε, hf⟩ := hf
  obtain ⟨hε', hg⟩ := hg
  have hpj : (0 : ℚ) < ((m : ℚ) + 2) ^ j := zpow_pos mTwo_pos j
  have hpj' : (0 : ℚ) < ((m : ℚ) + 2) ^ (-j) := zpow_pos mTwo_pos (-j)
  have hjj : ((m : ℚ) + 2) ^ j * ((m : ℚ) + 2) ^ (-j) = 1 := by
    rw [← zpow_add₀ mTwo_pos.ne', add_neg_cancel, zpow_zero]
  refine ⟨lt_min hε' (mul_pos hε hpj'), fun t ht1 ht2 => ?_⟩
  have h1 := min_le_left ε' (ε * ((m : ℚ) + 2) ^ (-j))
  have h2 := min_le_right ε' (ε * ((m : ℚ) + 2) ^ (-j))
  rw [Equiv.Perm.mul_apply, hg t (by linarith) ht2]
  have hhi : d + ((m : ℚ) + 2) ^ j * (t - d) ≤ d := by nlinarith
  have hlo : d - ε ≤ d + ((m : ℚ) + 2) ^ j * (t - d) := by
    have h3 : d - t ≤ ε * ((m : ℚ) + 2) ^ (-j) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hpj.le
    have e : ((m : ℚ) + 2) ^ j * (ε * ((m : ℚ) + 2) ^ (-j)) = ε := by
      linear_combination ε * hjj
    nlinarith
  rw [hf _ hlo hhi, zpow_add₀ mTwo_pos.ne']
  ring

theorem GermRight.inv (hf : GermRight m d i ε f) :
    GermRight m d (-i) (ε * ((m : ℚ) + 2) ^ i) f⁻¹ := by
  obtain ⟨hε, hf⟩ := hf
  have hpi : (0 : ℚ) < ((m : ℚ) + 2) ^ i := zpow_pos mTwo_pos i
  have hii : ((m : ℚ) + 2) ^ i * ((m : ℚ) + 2) ^ (-i) = 1 := by
    rw [← zpow_add₀ mTwo_pos.ne', add_neg_cancel, zpow_zero]
  refine ⟨mul_pos hε hpi, fun t ht1 ht2 => ?_⟩
  apply perm_inv_eq_of_apply_eq
  have hpi' : (0 : ℚ) < ((m : ℚ) + 2) ^ (-i) := zpow_pos mTwo_pos (-i)
  have hhi : d + ((m : ℚ) + 2) ^ (-i) * (t - d) ≤ d := by nlinarith
  have hlo : d - ε ≤ d + ((m : ℚ) + 2) ^ (-i) * (t - d) := by
    have h3 : d - t ≤ ε * ((m : ℚ) + 2) ^ i := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hpi'.le
    have e : ((m : ℚ) + 2) ^ (-i) * (ε * ((m : ℚ) + 2) ^ i) = ε := by
      linear_combination ε * hii
    nlinarith
  rw [hf _ hlo hhi]
  linear_combination (t - d) * hii

theorem GermLeft.mono {ε'' : ℚ} (hf : GermLeft m c i ε f) (h0 : 0 < ε'') (hle : ε'' ≤ ε) :
    GermLeft m c i ε'' f :=
  ⟨h0, fun t ht1 ht2 => hf.2 t ht1 (by linarith)⟩

theorem GermRight.mono {ε'' : ℚ} (hf : GermRight m d i ε f) (h0 : 0 < ε'') (hle : ε'' ≤ ε) :
    GermRight m d i ε'' f :=
  ⟨h0, fun t ht1 ht2 => hf.2 t (by linarith) ht2⟩

end GermAlgebra

/-- Affine pieces at a grid point, from the right and from the left. -/
theorem exists_germLeft {c d : ℚ} (hc : ∃ M, c ∈ Grid (m + 2) M) {f : Equiv.Perm ℚ}
    (hf : f ∈ rstab m c d) : ∃ i : ℤ, ∃ ε : ℚ, GermLeft m c i ε f := by
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, hf0, -⟩ := hf
  obtain ⟨Mc, k, hk⟩ := hc
  have hcast : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  let L := max N Mc
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ L := pow_pos mTwo_pos L
  have hinv : ((m : ℚ) + 2) ^ L * (((m : ℚ) + 2) ^ L)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  obtain ⟨k', hk'⟩ : ∃ k' : ℤ, c * ((m : ℚ) + 2) ^ L = k' := by
    refine ⟨k * ((m : ℤ) + 2) ^ (L - Mc), ?_⟩
    have e : ((m : ℚ) + 2) ^ L = ((m : ℚ) + 2) ^ Mc * ((m : ℚ) + 2) ^ (L - Mc) := by
      rw [← pow_add, Nat.add_sub_of_le (le_max_right N Mc)]
    rw [hcast] at hk
    rw [e, ← mul_assoc, hk]
    push_cast
    ring
  obtain ⟨s, ⟨i, rfl⟩, -, haff⟩ := hA.affine_fine (le_max_left N Mc) k'
  have hg0 : gridPt (m + 2) L k' = c := by
    simp only [gridPt, hcast]
    rw [← hk', mul_div_assoc, div_self hpos.ne', mul_one]
  have hg1 : gridPt (m + 2) L (k' + 1) = c + (((m : ℚ) + 2) ^ L)⁻¹ := by
    simp only [gridPt, hcast, div_eq_mul_inv]
    push_cast
    rw [← hk']
    linear_combination c * hinv
  refine ⟨i, (((m : ℚ) + 2) ^ L)⁻¹, inv_pos.mpr hpos, fun t ht1 ht2 => ?_⟩
  have h := haff t (by rw [hg0]; exact ht1) (by rw [hg1]; exact ht2)
  rw [hg0, hf0 c le_rfl] at h
  exact h

theorem exists_germRight {c d : ℚ} (hd : ∃ M, d ∈ Grid (m + 2) M) {f : Equiv.Perm ℚ}
    (hf : f ∈ rstab m c d) : ∃ j : ℤ, ∃ ε : ℚ, GermRight m d j ε f := by
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, -, hf1⟩ := hf
  obtain ⟨Md, k, hk⟩ := hd
  have hcast : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  let L := max N Md
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ L := pow_pos mTwo_pos L
  have hinv : ((m : ℚ) + 2) ^ L * (((m : ℚ) + 2) ^ L)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  obtain ⟨k', hk'⟩ : ∃ k' : ℤ, d * ((m : ℚ) + 2) ^ L = k' := by
    refine ⟨k * ((m : ℤ) + 2) ^ (L - Md), ?_⟩
    have e : ((m : ℚ) + 2) ^ L = ((m : ℚ) + 2) ^ Md * ((m : ℚ) + 2) ^ (L - Md) := by
      rw [← pow_add, Nat.add_sub_of_le (le_max_right N Md)]
    rw [hcast] at hk
    rw [e, ← mul_assoc, hk]
    push_cast
    ring
  obtain ⟨s, ⟨j, rfl⟩, -, haff⟩ := hA.affine_fine (le_max_left N Md) (k' - 1)
  have hg0 : gridPt (m + 2) L (k' - 1) = d - (((m : ℚ) + 2) ^ L)⁻¹ := by
    simp only [gridPt, hcast, div_eq_mul_inv]
    push_cast
    rw [← hk']
    linear_combination d * hinv
  have hg1 : gridPt (m + 2) L (k' - 1 + 1) = d := by
    rw [sub_add_cancel]
    simp only [gridPt, hcast]
    rw [← hk', mul_div_assoc, div_self hpos.ne', mul_one]
  have hεpos : (0 : ℚ) < (((m : ℚ) + 2) ^ L)⁻¹ := inv_pos.mpr hpos
  refine ⟨j, (((m : ℚ) + 2) ^ L)⁻¹, hεpos, fun t ht1 ht2 => ?_⟩
  have h := haff t (by rw [hg0]; exact ht1) (by rw [hg1]; exact ht2)
  have hb := haff d (by rw [hg0]; linarith) (le_of_eq hg1.symm)
  rw [hg0] at h hb
  rw [hf1 d le_rfl] at hb
  rw [h]
  linear_combination -hb

/-! ## `Rstab^c` -/

variable (m)

/-- `Rstab^c([c, d])`: elements of `Rstab([c, d])` that are the identity near `c` and near `d`. -/
def rstabc (c d : ℚ) : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ rstab m c d ∧ ∃ δ : ℚ, 0 < δ ∧ (∀ t : ℚ, t ≤ c + δ → f t = t) ∧
    ∀ t : ℚ, d - δ ≤ t → f t = t}
  one_mem' := ⟨(rstab m c d).one_mem, 1, one_pos, fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨hf, δf, hδf, hf0, hf1⟩ ⟨hg, δg, hδg, hg0, hg1⟩
    have hm1 := min_le_left δf δg
    have hm2 := min_le_right δf δg
    refine ⟨(rstab m c d).mul_mem hf hg, min δf δg, lt_min hδf hδg, fun t ht => ?_,
      fun t ht => ?_⟩
    · show f (g t) = t
      rw [hg0 t (by linarith), hf0 t (by linarith)]
    · show f (g t) = t
      rw [hg1 t (by linarith), hf1 t (by linarith)]
  inv_mem' := by
    rintro f ⟨hf, δ, hδ, hf0, hf1⟩
    refine ⟨(rstab m c d).inv_mem hf, δ, hδ, fun t ht => ?_, fun t ht => ?_⟩
    · rw [Equiv.Perm.inv_eq_iff_eq, hf0 t ht]
    · rw [Equiv.Perm.inv_eq_iff_eq, hf1 t ht]

variable {m}

theorem germLeft_zero_fix {c : ℚ} {ε : ℚ} {f : Equiv.Perm ℚ} (hf : GermLeft m c 0 ε f) {t : ℚ}
    (ht1 : c ≤ t) (ht2 : t ≤ c + ε) : f t = t := by
  rw [hf.2 t ht1 ht2, zpow_zero]
  ring

theorem germRight_zero_fix {d : ℚ} {ε : ℚ} {f : Equiv.Perm ℚ} (hf : GermRight m d 0 ε f) {t : ℚ}
    (ht1 : d - ε ≤ t) (ht2 : t ≤ d) : f t = t := by
  rw [hf.2 t ht1 ht2, zpow_zero]
  ring

/-- **Commutators of `Rstab([c, d])` are the identity near the endpoints.** -/
theorem commutator_le_rstabc {c d : ℚ} (hc : ∃ M, c ∈ Grid (m + 2) M)
    (hd : ∃ M, d ∈ Grid (m + 2) M) : ⁅rstab m c d, rstab m c d⁆ ≤ rstabc m c d := by
  have hsub : ∀ f ∈ rstab m c d, ∀ g ∈ rstab m c d, ⁅f, g⁆ ∈ rstabc m c d := by
    intro f hf g hg
    have hfg : ⁅f, g⁆ ∈ rstab m c d := by
      rw [commutatorElement_def]
      exact (rstab m c d).mul_mem ((rstab m c d).mul_mem ((rstab m c d).mul_mem hf hg)
        ((rstab m c d).inv_mem hf)) ((rstab m c d).inv_mem hg)
    obtain ⟨i₁, ε₁, hL₁⟩ := exists_germLeft hc hf
    obtain ⟨i₂, ε₂, hL₂⟩ := exists_germLeft hc hg
    obtain ⟨j₁, η₁, hR₁⟩ := exists_germRight hd hf
    obtain ⟨j₂, η₂, hR₂⟩ := exists_germRight hd hg
    obtain ⟨εL, hL⟩ : ∃ εL : ℚ, GermLeft m c 0 εL ⁅f, g⁆ := by
      have h := ((hL₁.mul hL₂).mul hL₁.inv).mul hL₂.inv
      have e : i₁ + i₂ + -i₁ + -i₂ = 0 := by ring
      rw [e] at h
      rw [commutatorElement_def]
      exact ⟨_, h⟩
    obtain ⟨εR, hR⟩ : ∃ εR : ℚ, GermRight m d 0 εR ⁅f, g⁆ := by
      have h := ((hR₁.mul hR₂).mul hR₁.inv).mul hR₂.inv
      have e : j₁ + j₂ + -j₁ + -j₂ = 0 := by ring
      rw [e] at h
      rw [commutatorElement_def]
      exact ⟨_, h⟩
    have hfix0 := hfg.2.1
    have hfix1 := hfg.2.2
    refine ⟨hfg, min εL εR, lt_min hL.1 hR.1, fun t ht => ?_, fun t ht => ?_⟩
    · rcases le_or_gt t c with htc | htc
      · exact hfix0 t htc
      · exact germLeft_zero_fix hL htc.le (by linarith [min_le_left εL εR])
    · rcases le_or_gt d t with htd | htd
      · exact hfix1 t htd
      · exact germRight_zero_fix hR (by linarith [min_le_right εL εR]) htd.le
  exact (Subgroup.commutator_le).mpr hsub

/-! ## Lemma 4.4 -/

/-- Conjugation by a strictly increasing `h ∈ PLGroup` moving `[a, b]` into `[c, d]` maps `Rstab([a, b])`
into `Rstab([c, d])`. -/
theorem conj_mem_rstab {h : Equiv.Perm ℚ} (hh : h ∈ PLGroup (m + 2) (powSlopes m)) {a b c d : ℚ}
    (hca : c ≤ h a) (hbd : h b ≤ d) {f : Equiv.Perm ℚ} (hf : f ∈ rstab m a b) :
    h * f * h⁻¹ ∈ rstab m c d := by
  obtain ⟨hfP, hf0, hf1⟩ := hf
  have hmono := hh.1
  refine ⟨(PLGroup (m + 2) (powSlopes m)).mul_mem ((PLGroup (m + 2) (powSlopes m)).mul_mem hh hfP)
    ((PLGroup (m + 2) (powSlopes m)).inv_mem hh), fun t ht => ?_, fun t ht => ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    have h1 : h⁻¹ t ≤ a := by
      by_contra hlt
      have h2 := hmono (not_le.mp hlt)
      rw [perm_apply_inv_self] at h2
      linarith
    rw [hf0 _ h1, perm_apply_inv_self]
  · simp only [Equiv.Perm.mul_apply]
    have h1 : b ≤ h⁻¹ t := by
      by_contra hlt
      have h2 := hmono (not_le.mp hlt)
      rw [perm_apply_inv_self] at h2
      linarith
    rw [hf1 _ h1, perm_apply_inv_self]

theorem rstab_mono {a b c d : ℚ} (hca : c ≤ a) (hbd : b ≤ d) : rstab m a b ≤ rstab m c d := by
  rintro f ⟨hfP, hf0, hf1⟩
  exact ⟨hfP, fun t ht => hf0 t (by linarith), fun t ht => hf1 t (by linarith)⟩

variable (m)

/-- **Hyde–Lodha, Lemma 4.4.**  For `0 < a < c < d < b < 1` in `ℤ[1/n]`, with `I = [a, b]` and
`J = [c, d]`: `Rstab(I)' ∩ Rstab^c(J) = Rstab(J)'`. -/
theorem rstab_commutator_inter_rstabc {a b c d : ℚ} (ha : ∃ M, a ∈ Grid (m + 2) M)
    (hb : ∃ M, b ∈ Grid (m + 2) M) (hc : ∃ M, c ∈ Grid (m + 2) M) (hd : ∃ M, d ∈ Grid (m + 2) M)
    (h0a : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b) (hb1 : b < 1) :
    ⁅rstab m a b, rstab m a b⁆ ⊓ rstabc m c d = ⁅rstab m c d, rstab m c d⁆ := by
  apply le_antisymm
  · rintro g ⟨hgI, ⟨-, δ, hδ, hg0, hg1⟩⟩
    have hw : 0 < min δ ((d - c) / 3) := lt_min hδ (by linarith)
    have hmin1 := min_le_left δ ((d - c) / 3)
    have hmin2 := min_le_right δ ((d - c) / 3)
    obtain ⟨a₁, ha₁1, ha₁2, ha₁⟩ :=
      exists_grid_mem_Ioo (m := m) (show c < c + min δ ((d - c) / 3) by linarith)
    obtain ⟨b₁, hb₁1, hb₁2, hb₁⟩ :=
      exists_grid_mem_Ioo (m := m) (show d - min δ ((d - c) / 3) < d by linarith)
    have hgW : SupportedIn g (Set.Ioo a₁ b₁) := by
      intro t ht
      by_cases hta : t ≤ a₁
      · exact hg0 t (by linarith)
      · have htb : b₁ ≤ t := by
          by_contra htb
          exact ht ⟨not_le.mp hta, not_le.mp htb⟩
        exact hg1 t (by linarith)
    -- the conjugator
    obtain ⟨a', ha'1, ha'2, hra', -⟩ := exists_resEq_mem_Ioo (m := m) ha (show c < a₁ by linarith)
    obtain ⟨α, hα1, hα2, hα⟩ := exists_grid_mem_Ioo (m := m) h0a
    obtain ⟨h₁, hh₁, h₁low, h₁high, h₁a⟩ := exists_move m hα ha₁ hra'.symm hα2
      (by linarith) (by linarith) ha'2
    obtain ⟨b', hb'1, hb'2, hrb', -⟩ := exists_resEq_mem_Ioo (m := m) hb (show b₁ < d by linarith)
    obtain ⟨β, hβ1, hβ2, hβ⟩ := exists_grid_mem_Ioo (m := m) hb1
    obtain ⟨h₂, hh₂, h₂low, h₂high, h₂b⟩ := exists_move m hb₁ hβ hrb'.symm (by linarith)
      hb'1 hβ1 (by linarith)
    have hhP : h₂ * h₁ ∈ PLGroup (m + 2) (powSlopes m) :=
      (PLGroup (m + 2) (powSlopes m)).mul_mem hh₂ hh₁
    have hha : (h₂ * h₁) a = a' := by
      rw [Equiv.Perm.mul_apply, h₁a, h₂low a' (by linarith)]
    have hhb : (h₂ * h₁) b = b' := by
      rw [Equiv.Perm.mul_apply, h₁high b (by linarith), h₂b]
    have hhW : SupportedIn (h₂ * h₁) (Set.Icc a₁ b₁)ᶜ := by
      intro t ht
      rw [Set.notMem_compl_iff] at ht
      rw [Equiv.Perm.mul_apply, h₁high t ht.1, h₂low t ht.2]
    have hdisj : Disjoint (Set.Ioo a₁ b₁) (Set.Icc a₁ b₁)ᶜ :=
      Set.disjoint_left.mpr fun t ht1 ht2 => ht2 ⟨ht1.1.le, ht1.2.le⟩
    have hcomm : Commute g (h₂ * h₁) := commute_of_supportedIn hgW hhW hdisj
    have hconj : (h₂ * h₁) * g * (h₂ * h₁)⁻¹ = g := by
      rw [hcomm.symm.eq, mul_inv_cancel_right]
    have hle : ⁅rstab m a b, rstab m a b⁆ ≤
        (⁅rstab m c d, rstab m c d⁆).comap (MulAut.conj (h₂ * h₁)).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro f₁ hf₁ f₂ hf₂
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator
        (conj_mem_rstab hhP (by rw [hha]; linarith) (by rw [hhb]; linarith) hf₁)
        (conj_mem_rstab hhP (by rw [hha]; linarith) (by rw [hhb]; linarith) hf₂)
    have h := hle hgI
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj] at h
    exact h
  · exact le_inf (Subgroup.commutator_mono (rstab_mono hac.le hdb.le) (rstab_mono hac.le hdb.le))
      (commutator_le_rstabc hc hd)

#audit_axioms GroupApproximation.HigmanThompson.commutator_le_rstabc
#audit_axioms GroupApproximation.HigmanThompson.rstab_commutator_inter_rstabc

end HigmanThompson
end GroupApproximation
