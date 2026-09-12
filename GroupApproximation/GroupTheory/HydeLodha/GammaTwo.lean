import GroupApproximation.GroupTheory.HigmanThompson.GridAffine
import GroupApproximation.Meta.AxiomGuard

/-!
# Hyde–Lodha's group `Γ₂`

Hyde and Lodha (Definition 1.2, `n = 2`, `η = 6`) define `Γ₂ ≤ Homeo⁺(ℝ)` as the piecewise linear
homeomorphisms `f` with breakpoints in `ℤ[1/6]` and `ℤ[1/6]·f = ℤ[1/6]`, commuting with `t ↦ t + 1`,
such that at every `x ∉ ℤ[1/6]` the slope is `2^i 3^j` with `i - j` the signed number of integers
between `x` and `f x`, i.e. `i - j = ⌊f x⌋ - ⌊x⌋`.

Here `Γ₂` is recorded through its action on `ℚ` (`gammaTwo`), in the grid-affine model of
`HigmanThompson.GridAffine`:

* `slopes23`: the slopes `2^i 3^j`;
* `HLCond f`: condition (3), at each `x ∉ ℤ[1/6]` some affine piece of `f` around `x` has slope
  `2^i 3^j` with `i - j = ⌊f x⌋ - ⌊x⌋`;
* `gammaTwo`: `PLGroup 6 slopes23`, `1`-periodic, satisfying `HLCond`, a subgroup of
  `Equiv.Perm ℚ` (the chain rule for slopes and `⌊f (g x)⌋ - ⌊x⌋ = (⌊f (g x)⌋ - ⌊g x⌋) +
  (⌊g x⌋ - ⌊x⌋)`, Hyde–Lodha Proposition 1.4(1)).
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

instance factOneLtSix : Fact (1 < 6) := ⟨by norm_num⟩

/-- The slopes `2^i 3^j`, `i, j ∈ ℤ`. -/
def slopes23 : Submonoid ℚ where
  carrier := {s | ∃ i j : ℤ, s = (2 : ℚ) ^ i * (3 : ℚ) ^ j}
  mul_mem' := by
    rintro a b ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    refine ⟨i + i', j + j', ?_⟩
    rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (3 : ℚ) ≠ 0)]
    ring
  one_mem' := ⟨0, 0, by simp⟩

/-- `x ∈ ℤ[1/6]`. -/
def Dyadic6 (x : ℚ) : Prop := ∃ N : ℕ, x ∈ Grid 6 N

/-- **Condition (3) of Hyde–Lodha.** -/
def HLCond (f : Equiv.Perm ℚ) : Prop :=
  ∀ x : ℚ, ¬ Dyadic6 x → ∃ a b : ℚ, ∃ i j : ℤ, a < x ∧ x < b ∧
    AffineOn f a b ((2 : ℚ) ^ i * (3 : ℚ) ^ j) ∧ i - j = ⌊f x⌋ - ⌊x⌋

/-! ## Affine pieces -/

theorem affineOn_comp {f g : ℚ → ℚ} {a₁ b₁ s₁ a₂ b₂ s₂ c d : ℚ} (hg : AffineOn g a₁ b₁ s₁)
    (hf : AffineOn f a₂ b₂ s₂) (hmono : Monotone g) (hc : a₁ ≤ c) (hd : d ≤ b₁) (hcd : c ≤ d)
    (hgc : a₂ ≤ g c) (hgd : g d ≤ b₂) : AffineOn (f ∘ g) c d (s₂ * s₁) := by
  intro t ht1 ht2
  have hgt1 : a₂ ≤ g t := le_trans hgc (hmono ht1)
  have hgt2 : g t ≤ b₂ := le_trans (hmono ht2) hgd
  have h1 := hf (g t) hgt1 hgt2
  have h2 := hf (g c) hgc (le_trans (hmono hcd) hgd)
  have h3 := hg t (le_trans hc ht1) (le_trans ht2 hd)
  have h4 := hg c hc (le_trans hcd hd)
  show f (g t) = f (g c) + s₂ * s₁ * (t - c)
  rw [h1, h2, h3, h4]
  ring

theorem affineOn_inv {f : Equiv.Perm ℚ} {a b s : ℚ} (hf : AffineOn f a b s) (hab : a ≤ b)
    (hs : s ≠ 0) (hmono : StrictMono f) : AffineOn ⇑f⁻¹ (f a) (f b) s⁻¹ := by
  intro w hw1 hw2
  have hfinv : ∀ y, f (f⁻¹ y) = y := fun y => Equiv.apply_symm_apply f y
  have hx1 : a ≤ f⁻¹ w := by
    by_contra h
    have h' := hmono (not_le.mp h)
    rw [hfinv] at h'
    linarith
  have hx2 : f⁻¹ w ≤ b := by
    by_contra h
    have h' := hmono (not_le.mp h)
    rw [hfinv] at h'
    linarith
  have h := hf (f⁻¹ w) hx1 hx2
  rw [hfinv] at h
  have ha : f⁻¹ (f a) = a := Equiv.symm_apply_apply f a
  rw [ha]
  have e : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  linear_combination -s⁻¹ * h + (f⁻¹ w - a) * e

/-- A permutation grid-affine together with its inverse moves no point of `ℚ ∖ ℤ[1/6]` into `ℤ[1/6]`. -/
theorem not_dyadic6_apply {f : Equiv.Perm ℚ} {Ω : Submonoid ℚ} {N B : ℕ}
    (hfi : GridAffine 6 Ω ⇑f⁻¹ N B) {x : ℚ} (hx : ¬ Dyadic6 x) : ¬ Dyadic6 (f x) := by
  rintro ⟨M, hM⟩
  apply hx
  have h := hfi.mapsGrid hM
  rw [Equiv.symm_apply_apply] at h
  exact ⟨_, h⟩

/-! ## The group -/

/-- **Hyde–Lodha's `Γ₂`**, acting on `ℚ`. -/
def gammaTwo : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ PLGroup 6 slopes23 ∧ (∀ t : ℚ, f (t + 1) = f t + 1) ∧ HLCond f}
  one_mem' := by
    refine ⟨(PLGroup 6 slopes23).one_mem, fun t => rfl, fun x _ => ?_⟩
    refine ⟨x - 1, x + 1, 0, 0, by linarith, by linarith, fun t _ _ => ?_, by simp⟩
    simp only [Equiv.Perm.one_apply, zpow_zero, mul_one]
    ring
  mul_mem' := by
    rintro f g ⟨hf, hfper, hfc⟩ ⟨hg, hgper, hgc⟩
    refine ⟨(PLGroup 6 slopes23).mul_mem hf hg, fun t => ?_, fun x hx => ?_⟩
    · show f (g (t + 1)) = f (g t) + 1
      rw [hgper, hfper]
    · obtain ⟨hgm, -, ⟨Ngi, Bgi, hgi⟩⟩ := hg
      obtain ⟨a₁, b₁, i₁, j₁, ha₁, hb₁, haff₁, hij₁⟩ := hgc x hx
      obtain ⟨a₂, b₂, i₂, j₂, ha₂, hb₂, haff₂, hij₂⟩ := hfc (g x) (not_dyadic6_apply hgi hx)
      have hginv : ∀ y, g (g⁻¹ y) = y := fun y => Equiv.apply_symm_apply g y
      have hc1 : g⁻¹ a₂ < x := by
        by_contra h
        have h' := hgm.monotone (not_lt.mp h)
        rw [hginv] at h'
        linarith
      have hd1 : x < g⁻¹ b₂ := by
        by_contra h
        have h' := hgm.monotone (not_lt.mp h)
        rw [hginv] at h'
        linarith
      refine ⟨max a₁ (g⁻¹ a₂), min b₁ (g⁻¹ b₂), i₂ + i₁, j₂ + j₁, max_lt ha₁ hc1, lt_min hb₁ hd1,
        ?_, ?_⟩
      · have hs : (2 : ℚ) ^ (i₂ + i₁) * (3 : ℚ) ^ (j₂ + j₁) =
            ((2 : ℚ) ^ i₂ * (3 : ℚ) ^ j₂) * ((2 : ℚ) ^ i₁ * (3 : ℚ) ^ j₁) := by
          rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (3 : ℚ) ≠ 0)]
          ring
        rw [hs]
        refine affineOn_comp haff₁ haff₂ hgm.monotone (le_max_left _ _) (min_le_left _ _)
          (le_trans (le_of_lt (max_lt ha₁ hc1)) (le_of_lt (lt_min hb₁ hd1))) ?_ ?_
        · have h := hgm.monotone (le_max_right a₁ (g⁻¹ a₂))
          rwa [hginv] at h
        · have h := hgm.monotone (min_le_right b₁ (g⁻¹ b₂))
          rwa [hginv] at h
      · show i₂ + i₁ - (j₂ + j₁) = ⌊f (g x)⌋ - ⌊x⌋
        omega
  inv_mem' := by
    rintro f ⟨hf, hfper, hfc⟩
    refine ⟨(PLGroup 6 slopes23).inv_mem hf, fun t => ?_, fun x hx => ?_⟩
    · rw [Equiv.Perm.inv_eq_iff_eq, hfper, Equiv.apply_symm_apply]
    · obtain ⟨hfm, ⟨Nf, Bf, hfA⟩, -⟩ := hf
      have hfinv : ∀ y, f (f⁻¹ y) = y := fun y => Equiv.apply_symm_apply f y
      have hy : ¬ Dyadic6 (f⁻¹ x) := by
        have hfA' : GridAffine 6 slopes23 ⇑(f⁻¹)⁻¹ Nf Bf := by simpa only [inv_inv] using hfA
        exact not_dyadic6_apply hfA' hx
      obtain ⟨a, b, i, j, ha, hb, haff, hij⟩ := hfc (f⁻¹ x) hy
      have hs0 : (2 : ℚ) ^ i * (3 : ℚ) ^ j ≠ 0 := by positivity
      refine ⟨f a, f b, -i, -j, ?_, ?_, ?_, ?_⟩
      · have h := hfm ha
        rwa [hfinv] at h
      · have h := hfm hb
        rwa [hfinv] at h
      · have hs : (2 : ℚ) ^ (-i) * (3 : ℚ) ^ (-j) = ((2 : ℚ) ^ i * (3 : ℚ) ^ j)⁻¹ := by
          rw [zpow_neg, zpow_neg, mul_inv]
        rw [hs]
        exact affineOn_inv haff (le_of_lt (lt_trans ha hb)) hs0 hfm
      · rw [hfinv] at hij
        omega

theorem mem_gammaTwo {f : Equiv.Perm ℚ} :
    f ∈ gammaTwo ↔ f ∈ PLGroup 6 slopes23 ∧ (∀ t : ℚ, f (t + 1) = f t + 1) ∧ HLCond f :=
  Iff.rfl

theorem gammaTwo_add_int {f : Equiv.Perm ℚ} (hf : f ∈ gammaTwo) (t : ℚ) (k : ℤ) :
    f (t + k) = f t + k := by
  obtain ⟨-, hper, -⟩ := hf
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : t + ((k + 1 : ℤ) : ℚ) = (t + k) + 1 := by push_cast; ring
    rw [e, hper, ih]
    push_cast
    ring
  | pred k ih =>
    have e : t + ((-(k : ℤ) - 1 : ℤ) : ℚ) + 1 = t + ((-(k : ℤ) : ℤ) : ℚ) := by push_cast; ring
    have h := hper (t + ((-(k : ℤ) - 1 : ℤ) : ℚ))
    rw [e, ih] at h
    push_cast at h ⊢
    linarith

#audit_axioms GroupApproximation.HydeLodha.mem_gammaTwo
#audit_axioms GroupApproximation.HydeLodha.gammaTwo_add_int

end HydeLodha
end GroupApproximation
