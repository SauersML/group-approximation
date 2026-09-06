import GroupApproximation.CharClass.CartanTermCases

/-!
# Reindexing the Cartan sum

The sum that comes out of composite B runs over the splittings of the resolution
index; the Cartan formula's sum runs over the squares' own indices.  The two are
related by sending a splitting to the difference from the first cochain's degree,
and the ranges match only after the out-of-range terms are dropped on both sides.

Both sets of dropped terms vanish for the same reason in the end, but by
different mechanisms: on the left because a cut cannot hand a factor more
vertices than the simplex has, on the right because the Steenrod square is
unstable.

## Main results

* `cartanTermL`, `cartanTermR` — the two summands.
* `cartan_sum_reindex` — **the two sums agree**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}} {p q : ℕ}
  (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
  (hα : cochainCoboundary (ZMod 2) X p α = 0)
  (hβ : cochainCoboundary (ZMod 2) X q β = 0)

/-- The summand indexed by a splitting of the resolution index. -/
noncomputable def cartanTermL (d e j' : ℕ) : TotalH X :=
  TotalH.of X (d + 1)
    (cocycleClass X (d + 1)
      (padCochain X (p + p - j' + (q + q - (e - j'))) (d + 1)
        (cupSqTerm X p q α β e j'))
      (padCochain_cocycle X _ (d + 1) _ (cupSqTerm_cocycle X p q α β hα hβ e j')))

/-- The summand indexed by the first square's own index. -/
noncomputable def cartanTermR (j i : ℕ) : TotalH X :=
  TotalH.of X (i + p) (Sq i (cocycleClass X p α hα))
    * TotalH.of X (j - i + q) (Sq (j - i) (cocycleClass X q β hβ))

theorem cartanTermL_eq_zero_of_lt (d e j' : ℕ) (h : p < j') :
    cartanTermL α β hα hβ d e j' = 0 :=
  totalOf_term_of_zero X p q α β hα hβ d e j'
    (cupSqTerm_eq_zero_left X p q α β e j' h)

theorem cartanTermL_eq_zero_of_lt' (d e j' : ℕ) (h : q < e - j') :
    cartanTermL α β hα hβ d e j' = 0 :=
  totalOf_term_of_zero X p q α β hα hβ d e j'
    (cupSqTerm_eq_zero_right X p q α β e j' h)

theorem cartanTermR_eq_zero_of_lt (j i : ℕ) (h : p < i) :
    cartanTermR α β hα hβ j i = 0 := by
  unfold cartanTermR
  rw [Sq_eq_zero_of_lt i p h, map_zero, zero_mul]

theorem cartanTermR_eq_zero_of_lt' (j i : ℕ) (h : q < j - i) :
    cartanTermR α β hα hβ j i = 0 := by
  unfold cartanTermR
  rw [Sq_eq_zero_of_lt (j - i) q h, map_zero, mul_zero]

/-- On the surviving range the two summands agree. -/
theorem cartanTermL_eq_cartanTermR (j d e j' : ℕ) (hj : j ≤ p + q)
    (hd : d + 1 = j + (p + q)) (he : e = p + q - j)
    (hj'e : j' ≤ e) (hj'p : j' ≤ p) (hej : e - j' ≤ q) :
    cartanTermL α β hα hβ d e j' = cartanTermR α β hα hβ j (p - j') := by
  unfold cartanTermL cartanTermR
  rw [totalOf_term_of_good X p q α β hα hβ d e j' hj'p hej (by omega),
    show q - (e - j') = j - (p - j') from by omega]

/-- **The two sums agree.** -/
theorem cartan_sum_reindex (j d e : ℕ) (hj : j ≤ p + q)
    (hd : d + 1 = j + (p + q)) (he : e = p + q - j) :
    ∑ j' ∈ Finset.range (e + 1), cartanTermL α β hα hβ d e j'
      = ∑ i ∈ Finset.range (j + 1), cartanTermR α β hα hβ j i := by
  classical
  have hAsub : (Finset.range (e + 1)).filter (fun j' => j' ≤ p ∧ e - j' ≤ q)
      ⊆ Finset.range (e + 1) := Finset.filter_subset _ _
  have hBsub : (Finset.range (j + 1)).filter (fun i => i ≤ p ∧ j - i ≤ q)
      ⊆ Finset.range (j + 1) := Finset.filter_subset _ _
  have hFz : ∀ x ∈ Finset.range (e + 1),
      x ∉ (Finset.range (e + 1)).filter (fun j' => j' ≤ p ∧ e - j' ≤ q) →
      cartanTermL α β hα hβ d e x = 0 := by
    intro x hx hxn
    have hxn' : ¬(x ≤ p ∧ e - x ≤ q) := fun h => hxn (Finset.mem_filter.mpr ⟨hx, h⟩)
    by_cases h1 : x ≤ p
    · exact cartanTermL_eq_zero_of_lt' α β hα hβ d e x (by omega)
    · exact cartanTermL_eq_zero_of_lt α β hα hβ d e x (by omega)
  have hGz : ∀ x ∈ Finset.range (j + 1),
      x ∉ (Finset.range (j + 1)).filter (fun i => i ≤ p ∧ j - i ≤ q) →
      cartanTermR α β hα hβ j x = 0 := by
    intro x hx hxn
    have hxn' : ¬(x ≤ p ∧ j - x ≤ q) := fun h => hxn (Finset.mem_filter.mpr ⟨hx, h⟩)
    by_cases h1 : x ≤ p
    · exact cartanTermR_eq_zero_of_lt' α β hα hβ j x (by omega)
    · exact cartanTermR_eq_zero_of_lt α β hα hβ j x (by omega)
  rw [← Finset.sum_subset hAsub hFz, ← Finset.sum_subset hBsub hGz]
  refine Finset.sum_bij' (fun j' _ => p - j') (fun i _ => p - i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb ⊢
    omega
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    omega
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    omega
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    exact cartanTermL_eq_cartanTermR α β hα hβ j d e a hj hd he
      (by omega) ha.2.1 ha.2.2

end

end GroupApproximation.CharClass
