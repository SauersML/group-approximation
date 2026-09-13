import GroupApproximation.GGT.OlshanskiiCutClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Antiparallel long pairs in geodesic polygons

`SidePair` (`OlshanskiiPolygonClasses`) leaves the relative direction of its
two segments open. `OrientedSidePair` fixes it: as the parameter on the first
side increases from `u` to `u'`, the corresponding parameter on the second side
decreases from `t'` to `t`. A loop reading both sides forwards reads the two
segments in opposite directions, the configuration planar surgery contradicts.

The transports of `SidePair` only translate parameters, so each has an oriented
counterpart with the same proof. An oriented pair is in particular a side pair.
-/

namespace GroupApproximation.Olshanskii

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.VanKampen.Estimating

universe v
variable {X : Type v} [PseudoMetricSpace X]

/-- Two antiparallel subsegments with long parameter intervals: `sides i u` is
close to `sides j t'` and `sides i u'` is close to `sides j t`, where `u < u'`
and `t < t'`. -/
def OrientedSidePair (vs : ℕ → X) (sides : ℕ → ℝ → X) (i j : ℕ) (β D : ℝ) : Prop :=
  ∃ u ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
    ∃ u' ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
      ∃ t ∈ Set.Icc (0 : ℝ) (dist (vs j) (vs (j + 1))),
        ∃ t' ∈ Set.Icc (0 : ℝ) (dist (vs j) (vs (j + 1))),
          β ≤ u' - u ∧ β ≤ t' - t ∧
            dist (sides i u) (sides j t') ≤ D ∧
            dist (sides i u') (sides j t) ≤ D

/-- The first side belongs to `A`, the other to `B`, they are distinct, and
they carry an antiparallel pair. -/
def OrientedClassPair (vs : ℕ → X) (sides : ℕ → ℝ → X) (n : ℕ)
    (A B : Set ℕ) (β D : ℝ) : Prop :=
  ∃ i < n, ∃ j < n, i ∈ A ∧ j ∈ B ∧ i ≠ j ∧ OrientedSidePair vs sides i j β D

theorem OrientedSidePair.toSidePair {vs : ℕ → X} {sides : ℕ → ℝ → X}
    {i j : ℕ} {β D : ℝ} (h : OrientedSidePair vs sides i j β D) :
    SidePair vs sides i j β D := by
  obtain ⟨u, hu, u', hu', t, ht, t', ht', hlen, hlen', hclose, hclose'⟩ := h
  refine ⟨u, hu, u', hu', t', ht', t, ht, le_trans hlen (le_abs_self _), ?_,
    hclose, hclose'⟩
  rw [abs_sub_comm]
  exact le_trans hlen' (le_abs_self _)

theorem OrientedClassPair.toClassPair {vs : ℕ → X} {sides : ℕ → ℝ → X}
    {n : ℕ} {A B : Set ℕ} {β D : ℝ} (h : OrientedClassPair vs sides n A B β D) :
    ClassPair vs sides n A B β D := by
  obtain ⟨i, hi, j, hj, hiA, hjB, hne, hp⟩ := h
  exact ⟨i, hi, j, hj, hiA, hjB, hne, hp.toSidePair⟩

/-- An antiparallel pair on restrictions lifts by translating both parameter
intervals. -/
theorem OrientedSidePair.of_restrictions
    {v w : ℕ → X} {p q : ℕ → ℝ → X} {i j a b : ℕ} {β D s t : ℝ}
    (h : OrientedSidePair v p i j β D)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hi : s + dist (v i) (v (i + 1)) ≤ dist (w a) (w (a + 1)))
    (hj : t + dist (v j) (v (j + 1)) ≤ dist (w b) (w (b + 1)))
    (hp : ∀ r ∈ Set.Icc (0 : ℝ) (dist (v i) (v (i + 1))), p i r = q a (s + r))
    (hq : ∀ r ∈ Set.Icc (0 : ℝ) (dist (v j) (v (j + 1))), p j r = q b (t + r)) :
    OrientedSidePair w q a b β D := by
  obtain ⟨u, hu, u', hu', r, hr, r', hr', hlen, hlen', hclose, hclose'⟩ := h
  refine ⟨s + u, ⟨by linarith [hu.1], by linarith [hu.2]⟩,
    s + u', ⟨by linarith [hu'.1], by linarith [hu'.2]⟩,
    t + r, ⟨by linarith [hr.1], by linarith [hr.2]⟩,
    t + r', ⟨by linarith [hr'.1], by linarith [hr'.2]⟩, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · simpa only [hp u hu, hq r' hr'] using hclose
  · simpa only [hp u' hu', hq r hr] using hclose'

theorem OrientedSidePair.of_rotation {vs : ℕ → X} {sides : ℕ → ℝ → X}
    {n i j : ℕ} {β D : ℝ} (hclose : vs n = vs 0)
    (h : OrientedSidePair (rotVertex vs n 0) (rotSide sides n 0) i j β D) :
    OrientedSidePair vs sides (wrapSide n i) (wrapSide n j) β D := by
  apply h.of_restrictions (s := 0) (t := 0) (by norm_num) (by norm_num)
  · simp only [zero_add, rotVertex_dist_eq_wrap hclose, le_refl]
  · simp only [zero_add, rotVertex_dist_eq_wrap hclose, le_refl]
  · intro r _
    simp only [rotSide_eq_wrap, zero_add]
  · intro r _
    simp only [rotSide_eq_wrap, zero_add]

theorem OrientedSidePair.of_innerCut
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {b n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides b n) (hba : b ≤ a)
    (hm : 1 ≤ m) (ham : a + m < b + n)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist (vs (a + m)) (vs (a + m + 1))))
    {cut : ℝ → X} {i j : ℕ} {β D : ℝ} (hi : i ≤ m) (hj : j ≤ m)
    (h : OrientedSidePair (innerVertex vs sides a m s t) (innerSide sides a m s cut)
      i j β D) : OrientedSidePair vs sides (a + i) (a + j) β D := by
  obtain ⟨u, hu, hui, hup⟩ := innerCut_restriction hpoly hba hm ham hs ht cut hi
  obtain ⟨r, hr, hrj, hrp⟩ := innerCut_restriction hpoly hba hm ham hs ht cut hj
  exact h.of_restrictions hu hr hui hrj (fun x _ => hup x) (fun x _ => hrp x)

theorem OrientedClassPair.of_innerCut
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides 0 n)
    (hm : 1 ≤ m) (ham : a + m < n)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist (vs (a + m)) (vs (a + m + 1))))
    {cut : ℝ → X} {A B : Set ℕ} {β D : ℝ}
    (h : OrientedClassPair (innerVertex vs sides a m s t) (innerSide sides a m s cut)
      (m + 2) (innerClass A a m) (innerClass B a m) β D) :
    OrientedClassPair vs sides n A B β D := by
  obtain ⟨i, _, j, _, hi, hj, hne, hp⟩ := h
  refine ⟨a + i, by dsimp [innerClass] at hi; omega,
    a + j, by dsimp [innerClass] at hj; omega, hi.2, hj.2,
    fun heq => hne (by omega), ?_⟩
  exact hp.of_innerCut hpoly (Nat.zero_le a) hm (by simpa using ham) hs ht hi.1 hj.1

/-- The other arc of a cut, read after rotating the polygon. -/
theorem OrientedClassPair.of_outerCut
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides 0 n)
    (hm : 1 ≤ m) (ham : a + m < n)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (dist (vs a) (vs (a + 1))))
    (ht : t ∈ Set.Icc (0 : ℝ) (dist (vs (a + m)) (vs (a + m + 1))))
    {cut : ℝ → X} {A B : Set ℕ} {β D : ℝ}
    (h : OrientedClassPair
      (innerVertex (rotVertex vs n 0) (rotSide sides n 0) (a + m) (n - m) t s)
      (innerSide (rotSide sides n 0) (a + m) (n - m) t cut)
      (n - m + 2) (innerClass (wrapSide n ⁻¹' A) (a + m) (n - m))
      (innerClass (wrapSide n ⁻¹' B) (a + m) (n - m)) β D) :
    OrientedClassPair vs sides n A B β D := by
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

end GroupApproximation.Olshanskii

#audit_axioms GroupApproximation.Olshanskii.OrientedSidePair.toSidePair
#audit_axioms GroupApproximation.Olshanskii.OrientedClassPair.toClassPair
#audit_axioms GroupApproximation.Olshanskii.OrientedSidePair.of_restrictions
#audit_axioms GroupApproximation.Olshanskii.OrientedSidePair.of_rotation
#audit_axioms GroupApproximation.Olshanskii.OrientedSidePair.of_innerCut
#audit_axioms GroupApproximation.Olshanskii.OrientedClassPair.of_innerCut
#audit_axioms GroupApproximation.Olshanskii.OrientedClassPair.of_outerCut
