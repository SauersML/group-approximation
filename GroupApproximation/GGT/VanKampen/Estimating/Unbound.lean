import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Unbound-arc estimates

This file proves the numerical parts of Osin's Appendix Lemmas 61 and 62.
For Lemma 61, the estimating graph has at most `12n` edges, so arcs of types
`A1` and `A2` number at most `29n`, arcs of type `A3` number at most `24n`,
and the total is at most `53n`.

For Lemma 62, if the total unbound length is at least `n * t`, where the
source later takes `t = sqrt rho`, then one complementary component has
unbound length at least its arc count times `t / 60`.  Cutting that component
into a disc gives at most four times as many sides, so the same component has
unbound length at least its side count times `t / 240`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

namespace UnboundEstimate

/-! ## Lemma 61 -/

/-- Osin Appendix Lemma 61, numerical count.  The hypotheses are the Euler
edge bound and the two arc-type counts obtained after cutting off relator
cells and distinguished contiguity regions. -/
theorem lemma61_arcCount_le
    (n r vertices edges typeA12 typeA3 : ℕ)
    (hn : 0 < n) (hr : r ≤ 4) (hvertices : vertices ≤ n + r)
    (hedges : edges ≤ 3 * (vertices - 1))
    (hA12 : typeA12 ≤ 2 * edges + n + r)
    (hA3 : typeA3 ≤ 2 * edges) :
    typeA12 + typeA3 ≤ 53 * n := by
  have hvertices' : vertices ≤ n + 4 := by omega
  have hedges' : edges ≤ 12 * n := by
    by_cases hverticesZero : vertices = 0
    · omega
    · have hverticesPos : 0 < vertices := Nat.pos_of_ne_zero hverticesZero
      have hnFour : 4 ≤ 4 * n := by omega
      omega
  have hA12' : typeA12 ≤ 29 * n := by omega
  have hA3' : typeA3 ≤ 24 * n := by omega
  omega

/-- The constants in Lemma 61 agree at the smallest permitted cell count:
`29 + 24 = 53` when `n = 1`. -/
theorem lemma61_constant_base : 29 * 1 + 24 * 1 = 53 * 1 := by
  norm_num

/-! ## Lemma 62: averaging -/

/-- If every component has less than its arc count times `t / 60`, then the
total unbound length is less than `n * t`.  The strict margin is the source's
`53 < 60`. -/
theorem total_lt_of_component_lt_sixty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (hcomponent : ∀ i : Fin d,
      unboundLength i < (arcCount i : ℝ) * t / 60) :
    (∑ i : Fin d, unboundLength i) < (n : ℝ) * t := by
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  by_cases hd : d = 0
  · subst d
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact mul_pos hnReal ht
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  have hsumStrict :
      (∑ i : Fin d, unboundLength i) <
        ∑ i : Fin d, (arcCount i : ℝ) * t / 60 := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
      hcomponent i
  have hcastCount :
      (∑ i : Fin d, (arcCount i : ℝ)) ≤ (53 * n : ℕ) := by
    exact_mod_cast hcount
  have hsumRewrite :
      (∑ i : Fin d, (arcCount i : ℝ) * t / 60) =
        (∑ i : Fin d, (arcCount i : ℝ)) * t / 60 := by
    calc
      (∑ i : Fin d, (arcCount i : ℝ) * t / 60) =
          ∑ i : Fin d, (arcCount i : ℝ) * (t / 60) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i : Fin d, (arcCount i : ℝ)) * (t / 60) := by
        rw [Finset.sum_mul]
      _ = (∑ i : Fin d, (arcCount i : ℝ)) * t / 60 := by ring
  rw [hsumRewrite] at hsumStrict
  have hscaled :
      (∑ i : Fin d, (arcCount i : ℝ)) * t / 60 ≤
        (53 * (n : ℝ)) * t / 60 := by
    have htNonneg : 0 ≤ t / 60 := by positivity
    have hcastCount' :
        (∑ i : Fin d, (arcCount i : ℝ)) ≤ 53 * (n : ℝ) := by
      norm_num at hcastCount ⊢
      exact hcastCount
    calc
      (∑ i : Fin d, (arcCount i : ℝ)) * t / 60 =
          (∑ i : Fin d, (arcCount i : ℝ)) * (t / 60) := by ring
      _ ≤ (53 * (n : ℝ)) * (t / 60) :=
        mul_le_mul_of_nonneg_right hcastCount' htNonneg
      _ = (53 * (n : ℝ)) * t / 60 := by ring
  have hmargin : (53 * (n : ℝ)) * t / 60 < (n : ℝ) * t := by
    nlinarith
  exact lt_of_lt_of_le hsumStrict (le_trans hscaled (le_of_lt hmargin))

/-- Osin Appendix Lemma 62, averaging form: a total of at least `n * t`
forces one component to meet the `1/60` density threshold. -/
theorem exists_component_ge_sixty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (htotal : (n : ℝ) * t ≤ ∑ i : Fin d, unboundLength i) :
    ∃ i : Fin d,
      (arcCount i : ℝ) * t / 60 ≤ unboundLength i := by
  by_contra hnone
  have hcomponent : ∀ i : Fin d,
      unboundLength i < (arcCount i : ℝ) * t / 60 := by
    intro i
    exact lt_of_not_ge fun hi => hnone ⟨i, hi⟩
  have hstrict := total_lt_of_component_lt_sixty n hn t ht arcCount
    unboundLength hcount hcomponent
  linarith

/-- Cutting a component into a disc introduces at most four sides per
original boundary arc, converting the `1/60` density to `1/240`. -/
theorem component_ge_twoForty
    {arcCount sideCount : ℕ} {unboundLength t : ℝ}
    (ht : 0 ≤ t) (hsides : sideCount ≤ 4 * arcCount)
    (hdense : (arcCount : ℝ) * t / 60 ≤ unboundLength) :
    (sideCount : ℝ) * t / 240 ≤ unboundLength := by
  have hsidesReal : (sideCount : ℝ) ≤ 4 * (arcCount : ℝ) := by
    exact_mod_cast hsides
  have htDiv : 0 ≤ t / 240 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hsidesReal htDiv
  calc
    (sideCount : ℝ) * t / 240 = (sideCount : ℝ) * (t / 240) := by ring
    _ ≤ (4 * (arcCount : ℝ)) * (t / 240) := hscaled
    _ = (arcCount : ℝ) * t / 60 := by ring
    _ ≤ unboundLength := hdense

/-- Combining the averaging and cutting steps gives the exact `1/240`
threshold used before the hyperbolic polygon lemma in Osin's proof. -/
theorem exists_component_ge_twoForty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount sideCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (hsides : ∀ i, sideCount i ≤ 4 * arcCount i)
    (htotal : (n : ℝ) * t ≤ ∑ i : Fin d, unboundLength i) :
    ∃ i : Fin d,
      (sideCount i : ℝ) * t / 240 ≤ unboundLength i := by
  obtain ⟨i, hi⟩ := exists_component_ge_sixty n hn t ht arcCount
    unboundLength hcount htotal
  exact ⟨i, component_ge_twoForty (le_of_lt ht) (hsides i) hi⟩

/-! ## Quasi-geodesic replacement lengths -/

/-- Replacing each of `m` unbound arcs by a geodesic loses at most `c` per
arc.  If these arcs have total length strictly greater than `k * t / 240`
and `m ≤ k`, their geodesic replacements have total length strictly greater
than `k * (lambda * t / 240 - c)`.  This is the displayed estimate for
`sigma_1` in Osin's proof of Lemma 62. -/
theorem replacement_total_gt
    {m k : ℕ} {lambda c t : ℝ}
    (arcLength replacementLength : Fin m → ℝ)
    (hlambda : 0 < lambda) (hc : 0 ≤ c) (hmk : m ≤ k)
    (hreplacement : ∀ i, lambda * arcLength i - c ≤ replacementLength i)
    (hdense : (k : ℝ) * t / 240 < ∑ i : Fin m, arcLength i) :
    (k : ℝ) * (lambda * t / 240 - c) <
      ∑ i : Fin m, replacementLength i := by
  have hterm :
      ∑ i : Fin m, (lambda * arcLength i - c) ≤
        ∑ i : Fin m, replacementLength i := by
    exact Finset.sum_le_sum fun i _ => hreplacement i
  have hsum :
      ∑ i : Fin m, (lambda * arcLength i - c) =
        lambda * (∑ i : Fin m, arcLength i) - (m : ℝ) * c := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    simp
  have hmkReal : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  have hpenalty : (m : ℝ) * c ≤ (k : ℝ) * c :=
    mul_le_mul_of_nonneg_right hmkReal hc
  rw [hsum] at hterm
  have hscaled : lambda * ((k : ℝ) * t / 240) <
      lambda * (∑ i : Fin m, arcLength i) :=
    mul_lt_mul_of_pos_left hdense hlambda
  calc
    (k : ℝ) * (lambda * t / 240 - c) =
        lambda * ((k : ℝ) * t / 240) - (k : ℝ) * c := by ring
    _ < lambda * (∑ i : Fin m, arcLength i) - (m : ℝ) * c := by
      linarith
    _ ≤ ∑ i : Fin m, replacementLength i := hterm

/-- If the side arcs have total length at most `eps * k`, the source's
choice `1000 * eps < a` makes their total strictly less than
`10⁻³ * a * k`, as required by Lemma `N123`. -/
theorem side_total_lt_oneThousandth
    {k : ℕ} {eps a sideTotal : ℝ}
    (hk : 0 < k) (hside : sideTotal ≤ eps * (k : ℝ))
    (hchoice : 1000 * eps < a) :
    sideTotal < (1 / 1000 : ℝ) * a * (k : ℝ) := by
  have hkReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hscale : eps * (k : ℝ) <
      (1 / 1000 : ℝ) * a * (k : ℝ) := by
    nlinarith
  exact lt_of_le_of_lt hside hscale

/-! ### Model checks -/

/-- The replacement estimate is exact in the one-arc zero-loss model. -/
theorem replacement_total_oneArcModel (t : ℝ) :
    (1 : ℝ) * t / 240 < t →
      (1 : ℝ) * ((1 : ℝ) * t / 240 - 0) < t := by
  intro ht
  simpa using replacement_total_gt
    (m := 1) (k := 1) (lambda := 1) (c := 0)
    (fun _ : Fin 1 => t) (fun _ : Fin 1 => t)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; simp) (by simpa using ht)

/-- The cutting conversion is exact at the smallest positive arc count. -/
theorem twoForty_constant_base (t : ℝ) :
    (4 : ℝ) * t / 240 = (1 : ℝ) * t / 60 := by
  ring

end UnboundEstimate

end VanKampen
end GGT
end GroupApproximation
