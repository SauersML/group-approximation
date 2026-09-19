import GroupApproximation.GGT.OlshanskiiCutClasses
import GroupApproximation.GGT.OlshanskiiBisection

/-!
# Balanced bisection with class accounting

This is the geometric producer for the uniform three-class polygon argument.
The two child polygons are the actual inner and outer cuts. Their class
lengths preserve original sides exactly, while the short class gains the
two copies of the geodesic diagonal.
-/

namespace GroupApproximation.Olshanskii

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.VanKampen.Estimating
open Finset
open scoped Classical

universe v
variable {X : Type v} [PseudoMetricSpace X]

/-- All geometric and class data of one balanced cut. -/
structure ClassifiedBisection (vs : ℕ → X) (sides : ℕ → ℝ → X)
    (n : ℕ) (δ : ℝ) where
  m : ℕ
  low : n ≤ 4 * m
  high : 4 * m ≤ 3 * n
  leftVertex : ℕ → X
  rightVertex : ℕ → X
  leftSide : ℕ → ℝ → X
  rightSide : ℕ → ℝ → X
  leftClass : Set ℕ → Set ℕ
  rightClass : Set ℕ → Set ℕ
  leftClosed : IsClosedPolygonAt leftVertex leftSide 0 (m + 2)
  rightClosed : IsClosedPolygonAt rightVertex rightSide 0 (n - m + 2)
  leftPair : ∀ A B β D, ClassPair leftVertex leftSide (m + 2)
    (leftClass A) (leftClass B) β D → ClassPair vs sides n A B β D
  rightPair : ∀ A B β D, ClassPair rightVertex rightSide (n - m + 2)
    (rightClass A) (rightClass B) β D → ClassPair vs sides n A B β D
  firstLength : ∀ A, classLength leftVertex (m + 2) (leftClass A) +
    classLength rightVertex (n - m + 2) (rightClass A) = classLength vs n A
  shortLength : ∀ B, classLength leftVertex (m + 2) (leftClass B)ᶜ +
    classLength rightVertex (n - m + 2) (rightClass B)ᶜ ≤
      classLength vs n Bᶜ + 12 * δ * ((Nat.clog 2 n : ℝ) + 1) + 2

private theorem classLength_as_weight (vs : ℕ → X) (n : ℕ) (A : Set ℕ) :
    classLength vs n A =
      ∑ i ∈ range n, dist (vs i) (vs (i + 1)) * (if i ∈ A then 1 else 0) := by
  classical
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp

private theorem innerClass_as_weight (v : ℕ → X) (a m : ℕ) (A : Set ℕ) :
    classLength v (m + 2) (innerClass A a m) =
      ∑ i ∈ range (m + 2), dist (v i) (v (i + 1)) *
        (if i ≤ m then (if a + i ∈ A then 1 else 0) else 0) := by
  classical
  rw [classLength_as_weight]
  apply sum_congr rfl
  intro i _
  by_cases him : i ≤ m <;> by_cases hiA : a + i ∈ A <;> simp [innerClass, him, hiA]

private theorem innerClass_compl_as_weight (v : ℕ → X) (a m : ℕ) (B : Set ℕ) :
    classLength v (m + 2) (innerClass B a m)ᶜ =
      ∑ i ∈ range (m + 2), dist (v i) (v (i + 1)) *
        (if i ≤ m then (if a + i ∈ Bᶜ then 1 else 0) else 1) := by
  classical
  rw [classLength_as_weight]
  apply sum_congr rfl
  intro i _
  by_cases him : i ≤ m <;> by_cases hiB : a + i ∈ B <;> simp [innerClass, him, hiB]

/-- The balanced-cut theorem supplies every field; no class-budget or
segment-lifting conclusion is assumed. -/
theorem exists_classifiedBisection {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n : ℕ}
    (hn : 9 ≤ n) (hpoly : IsClosedPolygonAt vs sides 0 n) :
    Nonempty (ClassifiedBisection vs sides n δ) := by
  classical
  have hside : IsSideFamily vs sides n := by
    intro i hi
    exact hpoly.1 i (Nat.zero_le i) (by simpa using hi)
  have hclose : vs n = vs 0 := by simpa only [zero_add] using hpoly.2
  obtain ⟨a, b, hab, hbn, hlow, hhigh, s, hs, t, ht, hdist⟩ :=
    exists_balanced_cut hδ hδ0 hgeo (show 8 ≤ n by omega)
      (Nat.le_pow_clog (by norm_num) n) vs sides hside hclose
  generalize hmdef : b - a = m at hlow hhigh
  have hb : b = a + m := by omega
  subst b
  have hm : 1 ≤ m := by omega
  have hmn : 1 ≤ n - m := by omega
  have hlow' : n ≤ 4 * m := by simpa only [Nat.add_sub_cancel_left] using hlow
  have hhigh' : 4 * m ≤ 3 * n := by simpa only [Nat.add_sub_cancel_left] using hhigh
  obtain ⟨cutL, hgL, hzL, heL⟩ := hgeo (sides (a + m) t) (sides a s)
  obtain ⟨cutR, hgR, hzR, heR⟩ := hgeo (sides a s) (sides (a + m) t)
  have hL := exists_innerCut_polygon hpoly (Nat.zero_le a) hm
    (show a + m < 0 + n by omega) hs.1 hs.2 ht.1 ht.2 hgL hzL heL
  have hrot := isClosedPolygonAt_rotate hpoly (Nat.zero_le (a + m))
    (show a + m ≤ 0 + n by omega)
  have hwa : wrapSide n (a + m + (n - m)) = a := by
    simp only [wrapSide, if_neg (show ¬ a + m + (n - m) < n by omega)]
    omega
  have hwb : wrapSide n (a + m) = a + m := by simp only [wrapSide, if_pos hbn]
  have hts : t ≤ dist (rotVertex vs n 0 (a + m))
      (rotVertex vs n 0 (a + m + 1)) := by
    simpa only [rotVertex_dist_eq_wrap hclose, hwb] using ht.2
  have hss : s ≤ dist (rotVertex vs n 0 (a + m + (n - m)))
      (rotVertex vs n 0 (a + m + (n - m) + 1)) := by
    simpa only [rotVertex_dist_eq_wrap hclose, hwa] using hs.2
  have hgR' : IsGeodesicSegment cutR 0
      (dist (rotSide sides n 0 (a + m + (n - m)) s)
        (rotSide sides n 0 (a + m) t)) := by
    simpa only [rotSide_eq_wrap, hwa, hwb] using hgR
  have hzR' : cutR 0 = rotSide sides n 0 (a + m + (n - m)) s := by
    simpa only [rotSide_eq_wrap, hwa] using hzR
  have heR' : cutR (dist (rotSide sides n 0 (a + m + (n - m)) s)
        (rotSide sides n 0 (a + m) t)) = rotSide sides n 0 (a + m) t := by
    simpa only [rotSide_eq_wrap, hwa, hwb] using heR
  have hR := exists_innerCut_polygon hrot (le_refl (a + m)) hmn
    (show a + m + (n - m) < a + m + n by omega) ht.1 hts hs.1 hss hgR' hzR' heR'
  let vL := innerVertex vs sides a m s t
  let vR := innerVertex (rotVertex vs n 0) (rotSide sides n 0) (a + m) (n - m) t s
  let ell := dist (sides (a + m) t) (sides a s)
  have hweights : ∀ (weight : ℕ → ℝ) (z : ℝ),
      (∑ i ∈ range (m + 2), dist (vL i) (vL (i + 1)) *
        (if i ≤ m then weight (a + i) else z)) +
      (∑ i ∈ range (n - m + 2), dist (vR i) (vR (i + 1)) *
        (if i ≤ n - m then weight (wrapSide n (a + m + i)) else z)) =
      (∑ i ∈ range n, dist (vs i) (vs (i + 1)) * weight i) + 2 * ell * z := by
    intro weight z
    have hwL := inner_weight_sum (fun i => dist (vs i) (vs (i + 1)))
      (fun i => dist (vL i) (vL (i + 1))) weight hm s t ell z
      hL.2.1 hL.2.2.1 hL.2.2.2.1 hL.2.2.2.2
    have hwR := inner_weight_sum
      (fun i => dist (rotVertex vs n 0 i) (rotVertex vs n 0 (i + 1)))
      (fun i => dist (vR i) (vR (i + 1))) (fun i => weight (wrapSide n i))
      hmn t s (dist (rotSide sides n 0 (a + m + (n - m)) s)
        (rotSide sides n 0 (a + m) t)) z
      hR.2.1 hR.2.2.1 hR.2.2.2.1 hR.2.2.2.2
    simp only [rotVertex_dist_eq_wrap hclose, rotSide_eq_wrap, hwa, hwb] at hwR
    rw [dist_comm (sides a s) (sides (a + m) t)] at hwR
    exact two_cut_weight_sum (fun i => dist (vs i) (vs (i + 1)))
      (fun i => dist (vL i) (vL (i + 1))) (fun i => dist (vR i) (vR (i + 1)))
      weight hbn s t ell z hwL hwR
  refine ⟨{
    m := m, low := hlow', high := hhigh'
    leftVertex := vL, rightVertex := vR
    leftSide := innerSide sides a m s cutL
    rightSide := innerSide (rotSide sides n 0) (a + m) (n - m) t cutR
    leftClass := fun A => innerClass A a m
    rightClass := fun A => innerClass (wrapSide n ⁻¹' A) (a + m) (n - m)
    leftClosed := hL.1, rightClosed := hR.1
    leftPair := fun _ _ _ _ h => h.of_innerCut hpoly hm hbn hs ht
    rightPair := fun _ _ _ _ h => h.of_outerCut hpoly hm hbn hs ht
    firstLength := ?_, shortLength := ?_ }⟩
  · intro A
    rw [innerClass_as_weight, innerClass_as_weight, classLength_as_weight]
    simpa only [Set.mem_preimage, mul_zero, add_zero] using
      hweights (fun i => if i ∈ A then 1 else 0) 0
  · intro B
    rw [innerClass_compl_as_weight, innerClass_compl_as_weight, classLength_as_weight]
    have hw := hweights (fun i => if i ∈ Bᶜ then 1 else 0) 1
    simp only [Set.mem_compl_iff, Set.mem_preimage, mul_one] at hw ⊢
    rw [hw]
    have hd : ell ≤ 6 * δ * ((Nat.clog 2 n : ℝ) + 1) + 1 := by
      simpa only [ell, dist_comm] using hdist
    linarith

end GroupApproximation.Olshanskii

#audit_axioms GroupApproximation.Olshanskii.exists_classifiedBisection
