import GroupApproximation.GGT.DGOLemma64
import GroupApproximation.GGT.ElementaryIndependence
import GroupApproximation.GGT.HyperbolicFreeGroupAH

/-!
# Two orbits with a shared start and close ends have a common power

`GGT/HullSCConeOffHeavyMatched.lean` turned the diameter hypothesis of geometric
separation into two long, endpoint-matched pairs of powers.  This module is the
step that consumes them: **two power orbits based at the same point, both long,
with terminal points close, force a common nonzero power of the two elements.**

## Why this is not already in the tree

`GGT/DGOQuasiAxis.lean` proves exactly this for two `PowerAxisSegment`s of
**one** element `h` --- `exists_common_zpow_of_long_orientedClose` --- which is
what Dahmani--Guirardel--Osin's Lemma 6.7 needs, because there the two segments
are two `G`-translates of a single quasi-axis.  Geometric separation of a
*family* `{E(g λ)}` is not that situation: for `λ ≠ μ` the two axes belong to
different elements, and the free loxodromy and WPD that the one-element version
gets from `h` are no longer free.

What survives unchanged is the argument.  That proof passes through
`ElementaryMorse.exists_common_zpow_of_forward_fellow_travel_of_wpd_bound`,
which already takes two *arbitrary* loxodromic elements, and uses the
one-element hypothesis only to produce loxodromy and WPD.  So the general
statement is the same three lines with those two supplied as hypotheses, and
that is what is proved below.  `GGT/DGOQuasiAxis.lean` is left alone.

## The argument

Both orbits start at `z`.  Take a geodesic from `z` to `a ^ n • z` and one from
`z` to `b ^ m • z`.  They share an initial point and their terminal points are
`E`-close, so `dist_same_parameter_le_of_geodesic_close_endpoints` --- the
quadrilateral estimate of DGO Lemma 6.4 --- puts them within `2(E + 6δ)` of
each other at every common parameter up to the shorter length.  That is
precisely the forward fellow-travel hypothesis, at the constant `C = 2(E + 6δ)`,
and the WPD pigeonhole then returns the common power.

The fellow-travel constant is therefore *not* the endpoint bound `E`: it is
`2(E + 6δ)`, and the `δ` term is not slack that a sharper estimate would remove.
Two geodesics with the same endpoints already diverge by a multiple of `δ` in
the middle.

## Signs

`exists_common_zpow_of_close_orbit_endpoints` is stated at natural exponents,
because that is the shape the fellow-travel core consumes.  The consumer has
integers of unknown sign --- step 1 hands over `i j k l : ℤ` and neither
`j - i` nor `l - k` has a known sign, and the two signs are independent --- so
`..._zpow` runs the natural-exponent form at the four combinations of `a^{±1}`
and `b^{±1}` and takes the largest of the four thresholds.  Replacing `a` by
`a⁻¹` only negates the exponent in the conclusion, which is what
`common_zpow_of_inv_left` and `common_zpow_of_inv_right` record.

The integer form takes acylindricity rather than WPD, and that is forced rather
than chosen: the four runs need WPD for `a` *and* for `a⁻¹`, and nothing in the
tree derives one from the other.  Acylindricity gives both through
`isWPDAt_of_isAcylindrical`, and the consumer has it —
`HullGeneratingSet.acylindrical`.

## Model tests

The conclusion is a genuine constraint and not a triviality: two distinct basis
elements of a free group have no common nonzero power at all, which
`not_exists_common_zpow_free_basis` proves by exponent sum.  So the hypotheses
of the theorems below must genuinely fail for the free basis pair, and no
weakening that made them satisfiable there could be sound.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## Sign bookkeeping -/

/-- Replacing the left element by its inverse only negates the left exponent. -/
theorem common_zpow_of_inv_left {a b : G}
    (h : ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a⁻¹ ^ p = b ^ r) :
    ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  obtain ⟨p, r, hp, hr, heq⟩ := h
  refine ⟨-p, r, neg_ne_zero.mpr hp, hr, ?_⟩
  rw [zpow_neg, ← inv_zpow]
  exact heq

/-- Replacing the right element by its inverse only negates the right
exponent. -/
theorem common_zpow_of_inv_right {a b : G}
    (h : ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b⁻¹ ^ r) :
    ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  obtain ⟨p, r, hp, hr, heq⟩ := h
  refine ⟨p, -r, hp, neg_ne_zero.mpr hr, ?_⟩
  rw [zpow_neg, ← inv_zpow]
  exact heq

/-! ## The natural-exponent form -/

/-- **Long orbits from a common basepoint with close ends share a power.**

`a` and `b` are loxodromic at `z`, `a` is WPD there, and the two orbit points
`a ^ n • z` and `b ^ m • z` are within `E` of each other while both lie at
distance at least `T` from `z`.  Then some nonzero power of `a` equals some
nonzero power of `b`.

The threshold `T` depends on `a`, `b`, `z`, `δ` and `E` only --- in particular
not on `n` or `m`, which is the uniformity the consumer needs, since it has to
choose its diameter bound before seeing the exponents that the diameter
hypothesis produces. -/
theorem exists_common_zpow_of_close_orbit_endpoints {δ E : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hE : 0 ≤ E) {a b : G} {z : X}
    (ha : IsLoxodromic a z) (hb : IsLoxodromic b z) (hwpd : IsWPDAt a z) :
    ∃ T : ℝ, 0 < T ∧ ∀ n m : ℕ,
      T ≤ dist z ((a ^ n) • z) → T ≤ dist z ((b ^ m) • z) →
      dist ((a ^ n) • z) ((b ^ m) • z) ≤ E →
      ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  obtain ⟨T, hT, hlong⟩ :=
    ElementaryMorse.exists_common_zpow_of_forward_fellow_travel_of_wpd_bound
      hδ hδ0 hgeo hiso (C := 2 * (E + 6 * δ)) (by linarith) ha hb hwpd
  refine ⟨T, hT, ?_⟩
  intro n m hn hm hend
  obtain ⟨f, hf, hf0, hf1⟩ := hgeo z ((a ^ n) • z)
  obtain ⟨q, hq, hq0, hq1⟩ := hgeo z ((b ^ m) • z)
  refine hlong n m f q hf hf0 hf1 hq hq0 hq1 hn hm ?_
  intro t ht0 htT
  refine dist_same_parameter_le_of_geodesic_close_endpoints (E := E) hδ hδ0 hgeo
    hE hf dist_nonneg hq dist_nonneg ?_ ?_ ⟨ht0, htT.trans hn⟩ ⟨ht0, htT.trans hm⟩
  · rw [hf0, hq0]
  · rw [hf1, hq1]
    exact hend

/-! ## The integer-exponent form -/

/-- **The same statement at integer exponents.**

The four sign combinations are run separately and the four thresholds are
maximised, which is why the hypothesis is acylindricity rather than WPD for
`a`: the runs with a negative left exponent need WPD for `a⁻¹`. -/
theorem exists_common_zpow_of_close_orbit_endpoints_zpow {δ E : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) (hE : 0 ≤ E)
    {a b : G} {z : X} (ha : IsLoxodromic a z) (hb : IsLoxodromic b z) :
    ∃ T : ℝ, 0 < T ∧ ∀ n m : ℤ,
      T ≤ dist z ((a ^ n) • z) → T ≤ dist z ((b ^ m) • z) →
      dist ((a ^ n) • z) ((b ^ m) • z) ≤ E →
      ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧ a ^ p = b ^ r := by
  have hai : IsLoxodromic a⁻¹ z := isLoxodromic_inv hiso ha
  have hbi : IsLoxodromic b⁻¹ z := isLoxodromic_inv hiso hb
  obtain ⟨T₁, hT₁, h₁⟩ := exists_common_zpow_of_close_orbit_endpoints
    hδ hδ0 hgeo hiso hE ha hb (isWPDAt_of_isAcylindrical hacy ha)
  obtain ⟨T₂, -, h₂⟩ := exists_common_zpow_of_close_orbit_endpoints
    hδ hδ0 hgeo hiso hE ha hbi (isWPDAt_of_isAcylindrical hacy ha)
  obtain ⟨T₃, -, h₃⟩ := exists_common_zpow_of_close_orbit_endpoints
    hδ hδ0 hgeo hiso hE hai hb (isWPDAt_of_isAcylindrical hacy hai)
  obtain ⟨T₄, -, h₄⟩ := exists_common_zpow_of_close_orbit_endpoints
    hδ hδ0 hgeo hiso hE hai hbi (isWPDAt_of_isAcylindrical hacy hai)
  have e₁ : T₁ ≤ max (max T₁ T₂) (max T₃ T₄) :=
    (le_max_left T₁ T₂).trans (le_max_left _ _)
  have e₂ : T₂ ≤ max (max T₁ T₂) (max T₃ T₄) :=
    (le_max_right T₁ T₂).trans (le_max_left _ _)
  have e₃ : T₃ ≤ max (max T₁ T₂) (max T₃ T₄) :=
    (le_max_left T₃ T₄).trans (le_max_right _ _)
  have e₄ : T₄ ≤ max (max T₁ T₂) (max T₃ T₄) :=
    (le_max_right T₃ T₄).trans (le_max_right _ _)
  refine ⟨max (max T₁ T₂) (max T₃ T₄),
    lt_max_iff.mpr (Or.inl (lt_max_iff.mpr (Or.inl hT₁))), ?_⟩
  intro n m hn hm hend
  rcases ElementaryMorse.zpow_eq_pow_toNat_or_inv a n with ⟨-, hna⟩ | ⟨-, hna⟩ <;>
    rcases ElementaryMorse.zpow_eq_pow_toNat_or_inv b m with ⟨-, hmb⟩ | ⟨-, hmb⟩ <;>
      rw [hna] at hn hend <;> rw [hmb] at hm hend
  · exact h₁ _ _ (e₁.trans hn) (e₁.trans hm) hend
  · exact common_zpow_of_inv_right (h₂ _ _ (e₂.trans hn) (e₂.trans hm) hend)
  · exact common_zpow_of_inv_left (h₃ _ _ (e₃.trans hn) (e₃.trans hm) hend)
  · exact common_zpow_of_inv_left
      (common_zpow_of_inv_right (h₄ _ _ (e₄.trans hn) (e₄.trans hm) hend))

/-! ## Model test -/

/-- **The conclusion has content.**  Two distinct basis elements of a free group
have no common nonzero power: the exponent sum in the first letter is `p` on the
left and `0` on the right.

So the hypotheses above cannot be satisfiable for a free basis pair, and any
weakening that made them satisfiable there would be unsound.  This is the test
that keeps the fellow-travel constant honest: it is what forbids replacing
`2(E + 6δ)` by something that two divergent geodesics could meet. -/
theorem not_exists_common_zpow_free_basis :
    ¬ ∃ p r : ℤ, p ≠ 0 ∧ r ≠ 0 ∧
      (FreeGroup.of (0 : Fin 2)) ^ p = (FreeGroup.of (1 : Fin 2)) ^ r := by
  rintro ⟨p, r, hp, -, heq⟩
  have h := congrArg (GGT.expVal (GGT.basisWeight (0 : Fin 2))) heq
  rw [GGT.expVal_zpow, GGT.expVal_zpow, GGT.expVal_of, GGT.expVal_of,
    GGT.basisWeight_self,
    GGT.basisWeight_of_ne (a := (0 : Fin 2)) (c := (1 : Fin 2)) (by decide)] at h
  simp only [mul_one, mul_zero] at h
  exact hp h

end HullSC
end GroupApproximation
