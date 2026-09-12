import GroupApproximation.GGT.HullSCUnionGeometryFactorInput

/-!
# Few syllables and a long letter

`finite_conjDisplacement_of_sylLength` bounds the conjugation displacement set
whenever `t` has many syllables.  This module bounds it in the complementary
case --- `t` has at most `m` syllables but large word length --- and combines the
two into a bound valid for every long `t`.

## The argument

`t` has at most `m` syllables and `|t| ≥ m · M + 1`, so
`exists_long_syllable` produces a splitting `t = c · of τ · r`, with both seams
free, in which `|τ| > M`.  For `k` displacing `1` and `t` by at most `ε`, the
branch-point estimate applied twice --- at the boundary `c` and at the boundary
`c · of τ` --- gives

    |c⁻¹ k c| ≤ ⌊ε⌋₊    and    |(of τ)⁻¹ (c⁻¹ k c) (of τ)| ≤ ⌊ε⌋₊ ,

so `conj_single_dichotomy` at `τ` leaves only its first alternative: taking
`M ≥ ε` rules out `2|τ| ≤ 2⌊ε⌋₊`.  Hence `c⁻¹ k c = of γ` for a letter `γ` of
`τ`'s own factor, and `k = c · of γ · c⁻¹` with

    |γ| ≤ ε    and    |τ⁻¹ γ τ| ≤ ε ,

which is the factor's two-point displacement set at `1` and `τ`, at distance
`|τ| > M ≥ R₀`.  Taking `M := max R₀ ε + 1` serves both purposes at once.  The
prefix `c` is determined by `t`, so the count is the factor's own `N₀` --- no
ball of the union alphabet is enumerated anywhere, and the letters of `c` are
read off `t` rather than chosen.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.FreeProductCyclic
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.Manuscript.NonMF.TorsionFree

section ShortBranch

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
  [∀ i, DecidableEq (G i)] {S : ∀ i, Set (G i)}

/-- **The displacement set of a `t` with few syllables and large length.**  Its
elements are conjugates, by a prefix of `t`, of the factor's own displacement
set at the two ends of `t`'s longest letter. -/
theorem finite_conjDisplacement_of_sylLength_le
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {A : Alphabet (CoprodI G)}
    (hA : A.carrier = unionCarrier S) {ε : ℝ} (hε : 0 < ε) (m : ℕ)
    {R₀ : ℝ} {N₀ : ℕ}
    (hfac : ∀ (i : ι) (τ : G i), R₀ ≤ ((wordNorm (S i) τ : ℕ) : ℝ) →
      {γ : G i | ((wordNorm (S i) γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm (S i) (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.Finite ∧
        {γ : G i | ((wordNorm (S i) γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm (S i) (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.ncard ≤ N₀)
    (t : CoprodI G) (hsyl : sylLength t ≤ m)
    (hR : (m : ℝ) * (max R₀ ε + 1) + 1
      ≤ ((wordNorm (unionCarrier S) t : ℕ) : ℝ)) :
    (conjDisplacement A ε t).Finite ∧
      (conjDisplacement A ε t).ncard ≤ N₀ := by
  classical
  have hMpos : (0 : ℝ) < max R₀ ε + 1 := by
    have hle : ε ≤ max R₀ ε := le_max_right _ _
    linarith
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, wordNorm_one] at hR
    have hm0 : (0 : ℝ) ≤ (m : ℝ) * (max R₀ ε + 1) :=
      mul_nonneg (Nat.cast_nonneg m) (le_of_lt hMpos)
    have hz : (((0 : ℕ)) : ℝ) = 0 := by norm_num
    rw [hz] at hR
    linarith
  obtain ⟨q, τ, c, r, hteq, hτ1, hcidx, hridx, -, hlong⟩ :=
    exists_long_syllable hS ht1
  -- the long letter is longer than `M`
  have hmul : wordNorm (unionCarrier S) t ≤ m * wordNorm (S q) τ :=
    le_trans hlong (Nat.mul_le_mul hsyl le_rfl)
  have hcast : ((wordNorm (unionCarrier S) t : ℕ) : ℝ)
      ≤ (m : ℝ) * ((wordNorm (S q) τ : ℕ) : ℝ) := by
    exact_mod_cast hmul
  have hτbig : max R₀ ε + 1 < ((wordNorm (S q) τ : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · exfalso
      rw [hm0] at hcast hR
      rw [Nat.cast_zero, zero_mul] at hcast
      rw [Nat.cast_zero, zero_mul, zero_add] at hR
      linarith
    · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      by_contra hcon
      push Not at hcon
      have hprod : (m : ℝ) * ((wordNorm (S q) τ : ℕ) : ℝ)
          ≤ (m : ℝ) * (max R₀ ε + 1) :=
        mul_le_mul_of_nonneg_left hcon (le_of_lt hmR)
      linarith
  have hτR₀ : R₀ ≤ ((wordNorm (S q) τ : ℕ) : ℝ) := by
    have hle : R₀ ≤ max R₀ ε := le_max_left _ _
    linarith
  have hτε : ⌊ε⌋₊ < wordNorm (S q) τ := by
    refine (Nat.floor_lt hε.le).mpr ?_
    have hle : ε ≤ max R₀ ε := le_max_right _ _
    linarith
  -- the two syllable boundaries
  have hseam1 : Word.fstIdx (Word.equiv c⁻¹)
      ≠ Word.fstIdx (Word.equiv (CoprodI.of τ * r)) := by
    rw [fstIdx_of_mul hτ1 hridx]
    exact hcidx
  have hteq' : t = c * (CoprodI.of τ * r) := by rw [hteq, mul_assoc]
  have hτinv : ((CoprodI.of τ : CoprodI G)⁻¹) = CoprodI.of τ⁻¹ :=
    (map_inv (CoprodI.of : G q →* CoprodI G) τ).symm
  have hseam2 : Word.fstIdx (Word.equiv (c * CoprodI.of τ)⁻¹)
      ≠ Word.fstIdx (Word.equiv r) := by
    have hrw : ((c * CoprodI.of τ)⁻¹ : CoprodI G) = CoprodI.of τ⁻¹ * c⁻¹ := by
      rw [mul_inv_rev, hτinv]
    rw [hrw, fstIdx_of_mul (inv_ne_one.mpr hτ1) hcidx]
    exact fun hcon => hridx hcon.symm
  -- every element of the displacement set is a conjugate of a letter of `G q`
  have hkey : ∀ k : CoprodI G, k ∈ conjDisplacement A ε t →
      ∃ γ : G q, k = c * CoprodI.of γ * c⁻¹ ∧
        ((wordNorm (S q) γ : ℕ) : ℝ) ≤ ε ∧
        ((wordNorm (S q) (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε := by
    rintro k ⟨hk1, hk2⟩
    rw [hA] at hk1 hk2
    have hkn : wordNorm (unionCarrier S) k ≤ ⌊ε⌋₊ := Nat.le_floor hk1
    have hktn : wordNorm (unionCarrier S) (t⁻¹ * k * t) ≤ ⌊ε⌋₊ := Nat.le_floor hk2
    have hB1 := wordNorm_conj_le_of_seam hS hseam1 k
    rw [← hteq'] at hB1
    have hg : wordNorm (unionCarrier S) (c⁻¹ * k * c) ≤ ⌊ε⌋₊ := by
      rcases hB1 with h | h
      · omega
      · omega
    have hB2 := wordNorm_conj_le_of_seam hS hseam2 k
    rw [← hteq] at hB2
    have hconj : ((c * CoprodI.of τ)⁻¹ * k * (c * CoprodI.of τ) : CoprodI G)
        = (CoprodI.of τ)⁻¹ * (c⁻¹ * k * c) * CoprodI.of τ := by group
    rw [hconj] at hB2
    have hgτ : wordNorm (unionCarrier S)
        ((CoprodI.of τ)⁻¹ * (c⁻¹ * k * c) * CoprodI.of τ) ≤ ⌊ε⌋₊ := by
      rcases hB2 with h | h
      · omega
      · omega
    rcases conj_single_dichotomy hS τ (c⁻¹ * k * c) with ⟨γ, hγ⟩ | hbad
    · refine ⟨γ, ?_, ?_, ?_⟩
      · have hk : k = c * (c⁻¹ * k * c) * c⁻¹ := by group
        rw [hγ] at hk
        exact hk
      · have h2 : wordNorm (S q) γ ≤ ⌊ε⌋₊ := by
          rw [← wordNorm_of_single_eq hS γ, ← hγ]
          exact hg
        calc ((wordNorm (S q) γ : ℕ) : ℝ)
            ≤ ((⌊ε⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
          _ ≤ ε := Nat.floor_le hε.le
      · have hof : (CoprodI.of (τ⁻¹ * γ * τ) : CoprodI G)
            = (CoprodI.of τ)⁻¹ * (c⁻¹ * k * c) * CoprodI.of τ := by
          rw [map_mul, map_mul, map_inv, ← hγ]
        have h2 : wordNorm (S q) (τ⁻¹ * γ * τ) ≤ ⌊ε⌋₊ := by
          rw [← wordNorm_of_single_eq hS (τ⁻¹ * γ * τ), hof]
          exact hgτ
        calc ((wordNorm (S q) (τ⁻¹ * γ * τ) : ℕ) : ℝ)
            ≤ ((⌊ε⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
          _ ≤ ε := Nat.floor_le hε.le
    · exact absurd hbad (by omega)
  -- the count
  obtain ⟨hfin, hcard⟩ := hfac q τ hτR₀
  have hsub : conjDisplacement A ε t
      ⊆ (fun γ : G q => c * CoprodI.of γ * c⁻¹) ''
        {γ : G q | ((wordNorm (S q) γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm (S q) (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε} := by
    intro k hk
    obtain ⟨γ, hkeq, h1, h2⟩ := hkey k hk
    exact ⟨γ, ⟨h1, h2⟩, hkeq.symm⟩
  refine ⟨Set.Finite.subset (hfin.image _) hsub, ?_⟩
  calc (conjDisplacement A ε t).ncard
      ≤ ((fun γ : G q => c * CoprodI.of γ * c⁻¹) ''
          {γ : G q | ((wordNorm (S q) γ : ℕ) : ℝ) ≤ ε ∧
            ((wordNorm (S q) (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ {γ : G q | ((wordNorm (S q) γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm (S q) (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.ncard :=
        Set.ncard_image_le hfin
    _ ≤ N₀ := hcard

/-- **The conjugation displacement set of the union alphabet is finite at every
long `t`.**  Many syllables is the crossing estimate; few syllables and large
length is the long letter and the factor's own acylindricity. -/
theorem exists_conjDisplacement_bound
    (hS : ∀ i, IsSymmetricGeneratingSet (S i)) {A : Alphabet (CoprodI G)}
    (hA : A.carrier = unionCarrier S) {ε : ℝ} (hε : 0 < ε)
    {R₀ : ℝ} {N₀ : ℕ}
    (hfac : ∀ (i : ι) (τ : G i), R₀ ≤ ((wordNorm (S i) τ : ℕ) : ℝ) →
      {γ : G i | ((wordNorm (S i) γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm (S i) (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.Finite ∧
        {γ : G i | ((wordNorm (S i) γ : ℕ) : ℝ) ≤ ε ∧
          ((wordNorm (S i) (τ⁻¹ * γ * τ) : ℕ) : ℝ) ≤ ε}.ncard ≤ N₀) :
    ∃ (R : ℝ) (N : ℕ), ∀ t : CoprodI G,
      R ≤ ((wordNorm (unionCarrier S) t : ℕ) : ℝ) →
        (conjDisplacement A ε t).Finite ∧
          (conjDisplacement A ε t).ncard ≤ N := by
  refine ⟨((2 * ⌊ε⌋₊ + 1 : ℕ) : ℝ) * (max R₀ ε + 1) + 1,
    max ((⌊ε⌋₊ + 2) * (⌊ε⌋₊ + 2)) N₀, ?_⟩
  intro t hR
  by_cases hbig : 2 * ⌊ε⌋₊ + 2 ≤ sylLength t
  · obtain ⟨hfin, hcard⟩ := finite_conjDisplacement_of_sylLength hS hA ε t hbig
    exact ⟨hfin, le_trans hcard (le_max_left _ _)⟩
  · have hsmall : sylLength t ≤ 2 * ⌊ε⌋₊ + 1 := by omega
    obtain ⟨hfin, hcard⟩ :=
      finite_conjDisplacement_of_sylLength_le hS hA hε (2 * ⌊ε⌋₊ + 1) hfac t
        hsmall hR
    exact ⟨hfin, le_trans hcard (le_max_right _ _)⟩

end ShortBranch

end HullSCUnionGeometry
end GroupApproximation
