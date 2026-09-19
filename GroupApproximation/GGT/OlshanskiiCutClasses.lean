import GroupApproximation.GGT.OlshanskiiPolygonClasses

/-!
# Class lengths and long pairs under an actual polygon cut

The cut side belongs to neither retained class. Every other child side is
an explicit restriction of one parent side. The length identity holds for
arbitrary weights, so it applies both to the first class and to the short
class, with the new diagonal assigned weight zero or one respectively.
-/

namespace GroupApproximation.Olshanskii

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.VanKampen.Estimating
open Finset

universe v
variable {X : Type v} [PseudoMetricSpace X]

def innerClass (A : Set ℕ) (a m : ℕ) : Set ℕ := {i | i ≤ m ∧ a + i ∈ A}

/-- Inherited child sides are restrictions, with their full parameter range
inside the original side's range. This includes both split sides. -/
theorem innerCut_restriction
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {b n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides b n) (hba : b ≤ a)
    (hm : 1 ≤ m) (ham : a + m < b + n)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist (vs (a + m)) (vs (a + m + 1))))
    (cut : ℝ → X) {i : ℕ} (hi : i ≤ m) :
    ∃ u : ℝ, 0 ≤ u ∧
      u + dist (innerVertex vs sides a m s t i)
          (innerVertex vs sides a m s t (i + 1)) ≤
        dist (vs (a + i)) (vs (a + i + 1)) ∧
      ∀ r : ℝ, innerSide sides a m s cut i r = sides (a + i) (u + r) := by
  by_cases hi0 : i = 0
  · subst i
    refine ⟨s, hs.1, ?_, ?_⟩
    · rw [innerVertex_zero, innerVertex_mid vs sides a m s t (le_refl 1) hm]
      obtain ⟨hg, _, he⟩ := hpoly.1 a hba (by omega)
      have hd := dist_cutPoint_endpoint hg hs.1 hs.2
      rw [he] at hd
      simpa only [add_zero, hd, add_sub_cancel] using
        (le_refl (dist (vs a) (vs (a + 1))))
    · intro r
      simp only [innerSide_zero, add_zero]
  by_cases him : i = m
  · subst i
    refine ⟨0, le_refl 0, ?_, ?_⟩
    · rw [innerVertex_mid vs sides a m s t hm (le_refl m), innerVertex_cutPoint]
      obtain ⟨hg, hzero, _⟩ := hpoly.1 (a + m) (by omega) ham
      have hd := dist_startPoint_cutPoint hg ht.1 ht.2
      rw [hzero] at hd
      simpa only [zero_add, hd] using ht.2
    · intro r
      simp only [innerSide_end sides a m s cut hm, zero_add]
  · refine ⟨0, le_refl 0, ?_, ?_⟩
    · rw [innerVertex_mid vs sides a m s t (by omega) hi,
        innerVertex_mid vs sides a m s t (by omega) (by omega)]
      simp only [zero_add, Nat.add_assoc, le_refl]
    · intro r
      simp only [innerSide_mid sides a m s cut (by omega : 1 ≤ i)
        (by omega : i < m), zero_add]

theorem SidePair.of_innerCut
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {b n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides b n) (hba : b ≤ a)
    (hm : 1 ≤ m) (ham : a + m < b + n)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist (vs (a + m)) (vs (a + m + 1))))
    {cut : ℝ → X} {i j : ℕ} {β D : ℝ} (hi : i ≤ m) (hj : j ≤ m)
    (h : SidePair (innerVertex vs sides a m s t) (innerSide sides a m s cut)
      i j β D) : SidePair vs sides (a + i) (a + j) β D := by
  obtain ⟨u, hu, hui, hup⟩ := innerCut_restriction hpoly hba hm ham hs ht cut hi
  obtain ⟨r, hr, hrj, hrp⟩ := innerCut_restriction hpoly hba hm ham hs ht cut hj
  exact h.of_restrictions hu hr hui hrj (fun x _ => hup x) (fun x _ => hrp x)

theorem ClassPair.of_innerCut
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides 0 n)
    (hm : 1 ≤ m) (ham : a + m < n)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist (vs (a + m)) (vs (a + m + 1))))
    {cut : ℝ → X} {A B : Set ℕ} {β D : ℝ}
    (h : ClassPair (innerVertex vs sides a m s t) (innerSide sides a m s cut)
      (m + 2) (innerClass A a m) (innerClass B a m) β D) :
    ClassPair vs sides n A B β D := by
  obtain ⟨i, _, j, _, hi, hj, hne, hp⟩ := h
  refine ⟨a + i, by dsimp [innerClass] at hi; omega,
    a + j, by dsimp [innerClass] at hj; omega, hi.2, hj.2,
    fun heq => hne (by omega), ?_⟩
  exact hp.of_innerCut hpoly (Nat.zero_le a) hm (by simpa using ham) hs ht hi.1 hj.1

/-- The weighted length formula for one piece of a cut. -/
theorem inner_weight_sum (len child weight : ℕ → ℝ) {a m : ℕ}
    (hm : 1 ≤ m) (s t d z : ℝ)
    (hzero : child 0 = len a - s)
    (hmid : ∀ i, 1 ≤ i → i < m → child i = len (a + i))
    (hend : child m = t) (hdiag : child (m + 1) = d) :
    (∑ i ∈ range (m + 2), child i * (if i ≤ m then weight (a + i) else z)) =
      (∑ i ∈ range m, len (a + i) * weight (a + i)) - s * weight a +
        t * weight (a + m) + d * z := by
  have hterm : ∀ i ∈ range m,
      child i * weight (a + i) =
        len (a + i) * weight (a + i) - if i = 0 then s * weight a else 0 := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [hzero, sub_mul]
    · rw [hmid i (by omega) (mem_range.mp hi), if_neg hi0, sub_zero]
  have hsum : (∑ i ∈ range m, child i * weight (a + i)) =
      (∑ i ∈ range m, len (a + i) * weight (a + i)) - s * weight a := by
    rw [sum_congr rfl hterm, sum_sub_distrib]
    simp only [sum_ite_eq', mem_range, show 0 < m by omega, if_pos]
  rw [show m + 2 = (m + 1) + 1 by omega, sum_range_succ, sum_range_succ]
  have hfirst : (∑ i ∈ range m, child i * (if i ≤ m then weight (a + i) else z)) =
      ∑ i ∈ range m, child i * weight (a + i) := by
    apply sum_congr rfl
    intro i hi
    rw [if_pos (by have := mem_range.mp hi; omega)]
  rw [hfirst, hsum, if_pos (le_refl m), if_neg (show ¬ m + 1 ≤ m by omega), hend, hdiag]

/-- The other arc uses the same restriction theorem after re-reading the
polygon. Its inherited side indices remain distinct across the seam. -/
theorem ClassPair.of_outerCut
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides 0 n)
    (hm : 1 ≤ m) (ham : a + m < n)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist (vs (a + m)) (vs (a + m + 1))))
    {cut : ℝ → X} {A B : Set ℕ} {β D : ℝ}
    (h : ClassPair
      (innerVertex (rotVertex vs n 0) (rotSide sides n 0) (a + m) (n - m) t s)
      (innerSide (rotSide sides n 0) (a + m) (n - m) t cut)
      (n - m + 2) (innerClass (wrapSide n ⁻¹' A) (a + m) (n - m))
      (innerClass (wrapSide n ⁻¹' B) (a + m) (n - m)) β D) :
    ClassPair vs sides n A B β D := by
  obtain ⟨i, _, j, _, hi, hj, hne, hp⟩ := h
  have hclose : vs n = vs 0 := by simpa only [zero_add] using hpoly.2
  have hrot := isClosedPolygonAt_rotate hpoly (Nat.zero_le (a + m))
    (show a + m ≤ 0 + n by omega)
  have hwrapa : wrapSide n (a + m + (n - m)) = a := by
    simp only [wrapSide, if_neg (show ¬ a + m + (n - m) < n by omega)]
    omega
  have hwrapb : wrapSide n (a + m) = a + m := by simp only [wrapSide, if_pos ham]
  have ht' : t ∈ Set.Icc (0 : ℝ)
      (dist (rotVertex vs n 0 (a + m)) (rotVertex vs n 0 (a + m + 1))) := by
    simpa only [rotVertex_dist_eq_wrap hclose, hwrapb] using ht
  have hs' : s ∈ Set.Icc (0 : ℝ)
      (dist (rotVertex vs n 0 (a + m + (n - m)))
        (rotVertex vs n 0 (a + m + (n - m) + 1))) := by
    simpa only [rotVertex_dist_eq_wrap hclose, hwrapa] using hs
  have hp' := (hp.of_innerCut hrot (le_refl (a + m)) (by omega) (by omega)
    ht' hs' hi.1 hj.1).of_rotation hclose
  have hii : a + m + i < a + m + n := by have := hi.1; omega
  have hjj : a + m + j < a + m + n := by have := hj.1; omega
  refine ⟨wrapSide n (a + m + i), wrapSide_lt ham hii,
    wrapSide n (a + m + j), wrapSide_lt ham hjj, hi.2, hj.2, ?_, hp'⟩
  intro heq
  have := wrapSide_injective (show a + m ≤ a + m + i by omega) hii
    (show a + m ≤ a + m + j by omega) hjj heq
  exact hne (by omega)

/-- Two complementary cyclic arcs account for each original side once. -/
theorem sum_cut_arcs (f : ℕ → ℝ) {n a m : ℕ} (ham : a + m < n) :
    (∑ i ∈ range m, f (a + i)) +
        (∑ i ∈ range (n - m), f (wrapSide n (a + m + i))) =
      ∑ i ∈ range n, f i := by
  have hsplit := sum_range_add (fun i => f (wrapSide n (a + i))) m (n - m)
  rw [show m + (n - m) = n by omega,
    sum_wrapSide f (show a ≤ n by omega)] at hsplit
  have hfirst : (∑ i ∈ range m, f (wrapSide n (a + i))) =
      ∑ i ∈ range m, f (a + i) := by
    apply sum_congr rfl
    intro i hi
    simp only [wrapSide, if_pos (show a + i < n by have := mem_range.mp hi; omega)]
  rw [hfirst] at hsplit
  simpa only [Nat.add_assoc] using hsplit.symm

/-- Exact accounting for both pieces, valid for arbitrary real side weights.
The two copies of the new diagonal each have weight `z`. -/
theorem two_cut_weight_sum (len left right weight : ℕ → ℝ) {n a m : ℕ}
    (ham : a + m < n) (s t d z : ℝ)
    (hleft : (∑ i ∈ range (m + 2), left i *
        (if i ≤ m then weight (a + i) else z)) =
      (∑ i ∈ range m, len (a + i) * weight (a + i)) - s * weight a +
        t * weight (a + m) + d * z)
    (hright : (∑ i ∈ range (n - m + 2), right i *
        (if i ≤ n - m then weight (wrapSide n (a + m + i)) else z)) =
      (∑ i ∈ range (n - m), len (wrapSide n (a + m + i)) *
          weight (wrapSide n (a + m + i))) - t * weight (a + m) +
        s * weight a + d * z) :
    (∑ i ∈ range (m + 2), left i * (if i ≤ m then weight (a + i) else z)) +
      (∑ i ∈ range (n - m + 2), right i *
        (if i ≤ n - m then weight (wrapSide n (a + m + i)) else z)) =
      (∑ i ∈ range n, len i * weight i) + 2 * d * z := by
  have hsum := sum_cut_arcs (fun i => len i * weight i) ham
  rw [hleft, hright]
  linarith

end GroupApproximation.Olshanskii

#audit_axioms GroupApproximation.Olshanskii.innerCut_restriction
#audit_axioms GroupApproximation.Olshanskii.ClassPair.of_innerCut
#audit_axioms GroupApproximation.Olshanskii.inner_weight_sum
#audit_axioms GroupApproximation.Olshanskii.ClassPair.of_outerCut
#audit_axioms GroupApproximation.Olshanskii.sum_cut_arcs
#audit_axioms GroupApproximation.Olshanskii.two_cut_weight_sum
