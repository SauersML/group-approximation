import GroupApproximation.GGT.OlshanskiiLemma25

/-!
# Cutting a closed geodesic polygon in two

Ol'shanskii's Lemma 25 (Mat. Sb. **182** (1991)) is proved by recursion: bisect
a polygon along a short cut until every piece has at most eight sides.
`Olshanskii.exists_balanced_cut` supplies the cut, and
`Estimating.bisection_side_counts_lt` shows the recursion terminates, but
nothing so far turns a cut into two polygons.  This file builds both.

Given a closed polygon read from `b0`, two side indices `a` and `a + m` inside
its range, a point at parameter `s` on side `a`, a point at parameter `s'` on
side `a + m`, and a geodesic joining those two points, the inner arc closes up
into a polygon with `m + 2` sides: the tail of side `a` after `s`, the
untouched sides between, the head of side `a + m` up to `s'`, and the cut.

The accounting the recursion needs comes out with it.  Every side strictly
between the two cut sides keeps its length; side `a` contributes its tail, of
length its own length minus `s`; side `a + m` contributes its head, of length
`s'`.  So the two parts of a split side have lengths summing to the original,
and a class of sides carried through a cut loses nothing except what the cut
itself adds.

The outer arc is the same construction applied to the polygon read from the
other cut side.  `isClosedPolygonAt_rotate` re-reads a closed polygon from any
of its vertices, spending the closing hypothesis exactly once, at the seam
where the side leaving the closing vertex is the side leaving the base one.
So `exists_outerCut_polygon` is `exists_innerCut_polygon` composed with it,
and the two pieces have `m + 2` and `n - m + 2` sides.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

open GroupApproximation.HullGeometry
open GroupApproximation.Olshanskii

universe v

/-! ## Restricting a geodesic to a shorter initial interval -/

/-- A geodesic on `[0, M]` is a geodesic on every shorter initial interval. -/
theorem isGeodesicSegment_restrict {X : Type v} [PseudoMetricSpace X]
    {f : ℝ → X} {M u : ℝ}
    (h : IsGeodesicSegment f 0 M) (hu : u ≤ M) :
    IsGeodesicSegment f 0 u := by
  intro s hs t ht
  exact h s ⟨hs.1, le_trans hs.2 hu⟩ t ⟨ht.1, le_trans ht.2 hu⟩

/-! ## The inner piece of a cut -/

/-- Vertices of the inner piece: the first cut point, then the vertices
between the two cut sides, then the second cut point, then back to the
first. -/
def innerVertex {X : Type v} (vs : ℕ → X) (sides : ℕ → ℝ → X)
    (a m : ℕ) (s s' : ℝ) : ℕ → X :=
  fun j =>
    if j = 0 then sides a s
    else if j ≤ m then vs (a + j)
    else if j = m + 1 then sides (a + m) s'
    else sides a s

/-- Sides of the inner piece: the tail of side `a`, the untouched sides, the
head of side `a + m`, and the cut. -/
def innerSide {X : Type v} (sides : ℕ → ℝ → X) (a m : ℕ) (s : ℝ)
    (cut : ℝ → X) : ℕ → ℝ → X :=
  fun j =>
    if j = 0 then (fun r => sides a (s + r))
    else if j < m then sides (a + j)
    else if j = m then sides (a + m)
    else cut

theorem innerVertex_zero {X : Type v} (vs : ℕ → X) (sides : ℕ → ℝ → X)
    (a m : ℕ) (s s' : ℝ) :
    innerVertex vs sides a m s s' 0 = sides a s := rfl

theorem innerVertex_mid {X : Type v} (vs : ℕ → X) (sides : ℕ → ℝ → X)
    (a m : ℕ) (s s' : ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ m) :
    innerVertex vs sides a m s s' j = vs (a + j) := by
  have h0 : ¬ (j = 0) := by omega
  show (if j = 0 then sides a s
      else if j ≤ m then vs (a + j)
      else if j = m + 1 then sides (a + m) s'
      else sides a s) = vs (a + j)
  rw [if_neg h0, if_pos hj2]

theorem innerVertex_cutPoint {X : Type v} (vs : ℕ → X) (sides : ℕ → ℝ → X)
    (a m : ℕ) (s s' : ℝ) :
    innerVertex vs sides a m s s' (m + 1) = sides (a + m) s' := by
  have h0 : ¬ (m + 1 = 0) := by omega
  have h1 : ¬ (m + 1 ≤ m) := by omega
  show (if m + 1 = 0 then sides a s
      else if m + 1 ≤ m then vs (a + (m + 1))
      else if m + 1 = m + 1 then sides (a + m) s'
      else sides a s) = sides (a + m) s'
  rw [if_neg h0, if_neg h1, if_pos rfl]

theorem innerVertex_last {X : Type v} (vs : ℕ → X) (sides : ℕ → ℝ → X)
    (a m : ℕ) (s s' : ℝ) :
    innerVertex vs sides a m s s' (m + 2) = sides a s := by
  have h0 : ¬ (m + 2 = 0) := by omega
  have h1 : ¬ (m + 2 ≤ m) := by omega
  have h2 : ¬ (m + 2 = m + 1) := by omega
  show (if m + 2 = 0 then sides a s
      else if m + 2 ≤ m then vs (a + (m + 2))
      else if m + 2 = m + 1 then sides (a + m) s'
      else sides a s) = sides a s
  rw [if_neg h0, if_neg h1, if_neg h2]

theorem innerSide_zero {X : Type v} (sides : ℕ → ℝ → X) (a m : ℕ) (s : ℝ)
    (cut : ℝ → X) :
    innerSide sides a m s cut 0 = fun r => sides a (s + r) := rfl

theorem innerSide_mid {X : Type v} (sides : ℕ → ℝ → X) (a m : ℕ) (s : ℝ)
    (cut : ℝ → X) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j < m) :
    innerSide sides a m s cut j = sides (a + j) := by
  have h0 : ¬ (j = 0) := by omega
  show (if j = 0 then (fun r => sides a (s + r))
      else if j < m then sides (a + j)
      else if j = m then sides (a + m)
      else cut) = sides (a + j)
  rw [if_neg h0, if_pos hj2]

theorem innerSide_end {X : Type v} (sides : ℕ → ℝ → X) (a m : ℕ) (s : ℝ)
    (cut : ℝ → X) (hm : 1 ≤ m) :
    innerSide sides a m s cut m = sides (a + m) := by
  have h0 : ¬ (m = 0) := by omega
  have h1 : ¬ (m < m) := by omega
  show (if m = 0 then (fun r => sides a (s + r))
      else if m < m then sides (a + m)
      else if m = m then sides (a + m)
      else cut) = sides (a + m)
  rw [if_neg h0, if_neg h1, if_pos rfl]

theorem innerSide_cut {X : Type v} (sides : ℕ → ℝ → X) (a m : ℕ) (s : ℝ)
    (cut : ℝ → X) :
    innerSide sides a m s cut (m + 1) = cut := by
  have h0 : ¬ (m + 1 = 0) := by omega
  have h1 : ¬ (m + 1 < m) := by omega
  have h2 : ¬ (m + 1 = m) := by omega
  show (if m + 1 = 0 then (fun r => sides a (s + r))
      else if m + 1 < m then sides (a + (m + 1))
      else if m + 1 = m then sides (a + m)
      else cut) = cut
  rw [if_neg h0, if_neg h1, if_neg h2]

/-! ## The two cut-point distances -/

/-- The tail of a side after parameter `s` has the side's length minus `s`. -/
theorem dist_cutPoint_endpoint {X : Type v} [PseudoMetricSpace X]
    {f : ℝ → X} {M s : ℝ}
    (h : IsGeodesicSegment f 0 M) (hs0 : 0 ≤ s) (hsM : s ≤ M) :
    dist (f s) (f M) = M - s := by
  rw [h s ⟨hs0, hsM⟩ M ⟨le_trans hs0 hsM, le_refl M⟩,
    abs_of_nonpos (by linarith : s - M ≤ 0)]
  ring

/-- The head of a side up to parameter `s'` has length `s'`. -/
theorem dist_startPoint_cutPoint {X : Type v} [PseudoMetricSpace X]
    {f : ℝ → X} {M s' : ℝ}
    (h : IsGeodesicSegment f 0 M) (hs0 : 0 ≤ s') (hsM : s' ≤ M) :
    dist (f 0) (f s') = s' := by
  rw [h 0 ⟨le_refl 0, le_trans hs0 hsM⟩ s' ⟨hs0, hsM⟩,
    abs_of_nonpos (by linarith : (0 : ℝ) - s' ≤ 0)]
  ring

/-! ## The cut -/

/-- **Cutting a closed geodesic polygon along a geodesic between points on two
of its sides.**  The inner arc, between side `a` and side `a + m`, closes into
a polygon with `m + 2` sides.  The last four conclusions are the length
accounting: the sides strictly between the cut sides are unchanged, and the
two cut sides contribute a tail of length `|side a| - s` and a head of length
`s'`, so the two parts of each split side add back up to it. -/
theorem exists_innerCut_polygon {X : Type v} [PseudoMetricSpace X]
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {b0 n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides b0 n)
    (hb0a : b0 ≤ a) (hm : 1 ≤ m) (hbn : a + m < b0 + n)
    {s s' : ℝ}
    (hs0 : 0 ≤ s) (hsM : s ≤ dist (vs a) (vs (a + 1)))
    (hs0' : 0 ≤ s') (hsM' : s' ≤ dist (vs (a + m)) (vs (a + m + 1)))
    {cut : ℝ → X}
    (hcut : IsGeodesicSegment cut 0 (dist (sides (a + m) s') (sides a s)))
    (hcut0 : cut 0 = sides (a + m) s')
    (hcut1 : cut (dist (sides (a + m) s') (sides a s)) = sides a s) :
    IsClosedPolygonAt (innerVertex vs sides a m s s')
        (innerSide sides a m s cut) 0 (m + 2) ∧
      dist (innerVertex vs sides a m s s' 0)
          (innerVertex vs sides a m s s' 1) =
        dist (vs a) (vs (a + 1)) - s ∧
      (∀ j, 1 ≤ j → j < m →
        dist (innerVertex vs sides a m s s' j)
            (innerVertex vs sides a m s s' (j + 1)) =
          dist (vs (a + j)) (vs (a + j + 1))) ∧
      dist (innerVertex vs sides a m s s' m)
          (innerVertex vs sides a m s s' (m + 1)) = s' ∧
      dist (innerVertex vs sides a m s s' (m + 1))
          (innerVertex vs sides a m s s' (m + 2)) =
        dist (sides (a + m) s') (sides a s) := by
  obtain ⟨hside, _hclose⟩ := hpoly
  obtain ⟨hgeoA, _hzeroA, hendA⟩ := hside a hb0a (by omega)
  obtain ⟨hgeoB, hzeroB, _hendB⟩ := hside (a + m) (by omega) (by omega)
  have htail0 : dist (sides a s) (sides a (dist (vs a) (vs (a + 1)))) =
      dist (vs a) (vs (a + 1)) - s := dist_cutPoint_endpoint hgeoA hs0 hsM
  rw [hendA] at htail0
  have hhead0 : dist (sides (a + m) 0) (sides (a + m) s') = s' :=
    dist_startPoint_cutPoint hgeoB hs0' hsM'
  rw [hzeroB] at hhead0
  have hv0 : innerVertex vs sides a m s s' 0 = sides a s :=
    innerVertex_zero vs sides a m s s'
  have hv1 : innerVertex vs sides a m s s' 1 = vs (a + 1) :=
    innerVertex_mid vs sides a m s s' (le_refl 1) hm
  have hvm : innerVertex vs sides a m s s' m = vs (a + m) :=
    innerVertex_mid vs sides a m s s' hm (le_refl m)
  have hvm1 : innerVertex vs sides a m s s' (m + 1) = sides (a + m) s' :=
    innerVertex_cutPoint vs sides a m s s'
  have hvm2 : innerVertex vs sides a m s s' (m + 2) = sides a s :=
    innerVertex_last vs sides a m s s'
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i _hi0 hi
    have him : i < m + 2 := by omega
    rcases Nat.lt_or_ge i 1 with hlow | hlow
    · have hi0 : i = 0 := by omega
      rw [hi0, innerSide_zero, hv0, hv1, htail0]
      refine ⟨?_, ?_, ?_⟩
      · exact isGeodesicSegment_shift (f := sides a)
          (M := dist (vs a) (vs (a + 1))) (u := s)
          (u' := dist (vs a) (vs (a + 1))) hgeoA hs0 (le_refl _)
      · show sides a (s + 0) = sides a s
        rw [add_zero]
      · show sides a (s + (dist (vs a) (vs (a + 1)) - s)) = vs (a + 1)
        rw [show s + (dist (vs a) (vs (a + 1)) - s)
            = dist (vs a) (vs (a + 1)) from by ring]
        exact hendA
    rcases Nat.lt_or_ge i m with hmid | hmid
    · have hva : innerVertex vs sides a m s s' i = vs (a + i) :=
        innerVertex_mid vs sides a m s s' hlow (le_of_lt hmid)
      have hvb : innerVertex vs sides a m s s' (i + 1) = vs (a + (i + 1)) :=
        innerVertex_mid vs sides a m s s' (by omega) (by omega)
      have harg : a + (i + 1) = a + i + 1 := by omega
      rw [innerSide_mid sides a m s cut hlow hmid, hva, hvb, harg]
      exact hside (a + i) (by omega) (by omega)
    rcases Nat.lt_or_ge i (m + 1) with hend | hend
    · have him' : i = m := by omega
      rw [him', innerSide_end sides a m s cut hm, hvm, hvm1, hhead0]
      exact ⟨isGeodesicSegment_restrict hgeoB hsM', hzeroB, rfl⟩
    · have him' : i = m + 1 := by omega
      rw [him', innerSide_cut, hvm1, hvm2]
      exact ⟨hcut, hcut0, hcut1⟩
  · show innerVertex vs sides a m s s' (0 + (m + 2)) =
      innerVertex vs sides a m s s' 0
    rw [show 0 + (m + 2) = m + 2 from by omega, hvm2, hv0]
  · rw [hv0, hv1]
    exact htail0
  · intro j hj1 hj2
    have hva : innerVertex vs sides a m s s' j = vs (a + j) :=
      innerVertex_mid vs sides a m s s' hj1 (le_of_lt hj2)
    have hvb : innerVertex vs sides a m s s' (j + 1) = vs (a + (j + 1)) :=
      innerVertex_mid vs sides a m s s' (by omega) (by omega)
    have harg : a + (j + 1) = a + j + 1 := by omega
    rw [hva, hvb, harg]
  · rw [hvm, hvm1]
    exact hhead0
  · rw [hvm1, hvm2]

/-! ## Reading a closed polygon from another of its vertices -/

/-- Vertices of a closed polygon re-read from a later index: past the closing
vertex the enumeration wraps back by `n`. -/
def rotVertex {X : Type v} (vs : ℕ → X) (n b0 : ℕ) : ℕ → X :=
  fun j => if j ≤ b0 + n then vs j else vs (j - n)

/-- Sides of a closed polygon re-read from a later index. -/
def rotSide {X : Type v} (sides : ℕ → ℝ → X) (n b0 : ℕ) : ℕ → ℝ → X :=
  fun j => if j < b0 + n then sides j else sides (j - n)

theorem rotVertex_of_le {X : Type v} (vs : ℕ → X) (n b0 : ℕ) {j : ℕ}
    (hj : j ≤ b0 + n) : rotVertex vs n b0 j = vs j := by
  show (if j ≤ b0 + n then vs j else vs (j - n)) = vs j
  rw [if_pos hj]

theorem rotVertex_of_gt {X : Type v} (vs : ℕ → X) (n b0 : ℕ) {j : ℕ}
    (hj : b0 + n < j) : rotVertex vs n b0 j = vs (j - n) := by
  have h : ¬ (j ≤ b0 + n) := by omega
  show (if j ≤ b0 + n then vs j else vs (j - n)) = vs (j - n)
  rw [if_neg h]

theorem rotSide_of_lt {X : Type v} (sides : ℕ → ℝ → X) (n b0 : ℕ) {j : ℕ}
    (hj : j < b0 + n) : rotSide sides n b0 j = sides j := by
  show (if j < b0 + n then sides j else sides (j - n)) = sides j
  rw [if_pos hj]

theorem rotSide_of_ge {X : Type v} (sides : ℕ → ℝ → X) (n b0 : ℕ) {j : ℕ}
    (hj : b0 + n ≤ j) : rotSide sides n b0 j = sides (j - n) := by
  have h : ¬ (j < b0 + n) := by omega
  show (if j < b0 + n then sides j else sides (j - n)) = sides (j - n)
  rw [if_neg h]

/-- **A closed geodesic polygon may be read from any of its vertices.**  The
only place the argument spends the closing hypothesis is the seam, where the
side leaving the closing vertex is the side leaving the base vertex. -/
theorem isClosedPolygonAt_rotate {X : Type v} [PseudoMetricSpace X]
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {b0 n k : ℕ}
    (hpoly : IsClosedPolygonAt vs sides b0 n)
    (hk0 : b0 ≤ k) (hkn : k ≤ b0 + n) :
    IsClosedPolygonAt (rotVertex vs n b0) (rotSide sides n b0) k n := by
  obtain ⟨hside, hclose⟩ := hpoly
  refine ⟨?_, ?_⟩
  · intro i hki hin
    rcases Nat.lt_or_ge i (b0 + n) with hlt | hge
    · rw [rotSide_of_lt sides n b0 hlt,
        rotVertex_of_le vs n b0 (by omega : i ≤ b0 + n),
        rotVertex_of_le vs n b0 (by omega : i + 1 ≤ b0 + n)]
      exact hside i (by omega) hlt
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · have hi : i = b0 + n := heq.symm
      rw [hi, rotSide_of_ge sides n b0 (le_refl (b0 + n)),
        show b0 + n - n = b0 from by omega,
        rotVertex_of_le vs n b0 (le_refl (b0 + n)),
        rotVertex_of_gt vs n b0 (by omega : b0 + n < b0 + n + 1),
        show b0 + n + 1 - n = b0 + 1 from by omega, hclose]
      exact hside b0 (le_refl b0) (by omega)
    · rw [rotSide_of_ge sides n b0 (by omega : b0 + n ≤ i),
        rotVertex_of_gt vs n b0 hgt,
        rotVertex_of_gt vs n b0 (by omega : b0 + n < i + 1),
        show i + 1 - n = i - n + 1 from by omega]
      exact hside (i - n) (by omega) (by omega)
  · rcases Nat.eq_or_lt_of_le hk0 with heq | hgt
    · have hk : k = b0 := heq.symm
      rw [hk, rotVertex_of_le vs n b0 (le_refl (b0 + n)),
        rotVertex_of_le vs n b0 (by omega : b0 ≤ b0 + n)]
      exact hclose
    · rw [rotVertex_of_gt vs n b0 (by omega : b0 + n < k + n),
        rotVertex_of_le vs n b0 hkn,
        show k + n - n = k from by omega]

/-- Past the closing vertex, index `a + n` of the re-read polygon is the
original vertex `a`.  At the base vertex this is the closing hypothesis; past
it, it is the wrap. -/
theorem rotVertex_wrap {X : Type v} (vs : ℕ → X) {n b0 a : ℕ}
    (hclose : vs (b0 + n) = vs b0) (hb0a : b0 ≤ a) :
    rotVertex vs n b0 (a + n) = vs a := by
  rcases Nat.eq_or_lt_of_le hb0a with heq | hgt
  · have ha : a = b0 := heq.symm
    rw [ha, rotVertex_of_le vs n b0 (le_refl (b0 + n))]
    exact hclose
  · rw [rotVertex_of_gt vs n b0 (by omega : b0 + n < a + n),
      show a + n - n = a from by omega]

/-- **The outer piece of the same cut.**  Reading the polygon from the second
cut side turns the outer arc into an inner arc, so the same construction gives
a closed polygon with `n - m + 2` sides. -/
theorem exists_outerCut_polygon {X : Type v} [PseudoMetricSpace X]
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {b0 n a m : ℕ}
    (hpoly : IsClosedPolygonAt vs sides b0 n)
    (hb0a : b0 ≤ a) (hm : 1 ≤ m) (hbn : a + m < b0 + n)
    {s s' : ℝ}
    (hs0 : 0 ≤ s) (hsM : s ≤ dist (vs a) (vs (a + 1)))
    (hs0' : 0 ≤ s') (hsM' : s' ≤ dist (vs (a + m)) (vs (a + m + 1)))
    {cut : ℝ → X}
    (hcut : IsGeodesicSegment cut 0 (dist (sides a s) (sides (a + m) s')))
    (hcut0 : cut 0 = sides a s)
    (hcut1 : cut (dist (sides a s) (sides (a + m) s')) = sides (a + m) s') :
    IsClosedPolygonAt
      (innerVertex (rotVertex vs n b0) (rotSide sides n b0)
        (a + m) (n - m) s' s)
      (innerSide (rotSide sides n b0) (a + m) (n - m) s' cut)
      0 (n - m + 2) := by
  have hclose := hpoly.2
  have hpoly' := isClosedPolygonAt_rotate hpoly (by omega : b0 ≤ a + m)
    (by omega : a + m ≤ b0 + n)
  have harg : a + m + (n - m) = a + n := by omega
  have hva : rotVertex vs n b0 (a + m) = vs (a + m) :=
    rotVertex_of_le vs n b0 (by omega)
  have hva1 : rotVertex vs n b0 (a + m + 1) = vs (a + m + 1) :=
    rotVertex_of_le vs n b0 (by omega)
  have hvb : rotVertex vs n b0 (a + m + (n - m)) = vs a := by
    rw [harg]
    exact rotVertex_wrap vs hclose hb0a
  have hvb1 : rotVertex vs n b0 (a + m + (n - m) + 1) = vs (a + 1) := by
    rw [harg, rotVertex_of_gt vs n b0 (by omega : b0 + n < a + n + 1),
      show a + n + 1 - n = a + 1 from by omega]
  have hsa : rotSide sides n b0 (a + m) = sides (a + m) :=
    rotSide_of_lt sides n b0 (by omega)
  have hsb : rotSide sides n b0 (a + m + (n - m)) = sides a := by
    rw [harg, rotSide_of_ge sides n b0 (by omega : b0 + n ≤ a + n),
      show a + n - n = a from by omega]
  refine (exists_innerCut_polygon hpoly' (le_refl (a + m)) (by omega)
    (by omega) hs0' ?_ hs0 ?_ ?_ ?_ ?_).1
  · rw [hva, hva1]
    exact hsM'
  · rw [hvb, hvb1]
    exact hsM
  · rw [hsb, hsa]
    exact hcut
  · rw [hsb]
    exact hcut0
  · rw [hsb, hsa]
    exact hcut1

/-! ## Model check -/

/-- A quadrilateral cut between side `0` and side `2` gives an inner piece of
four sides: the tail of side `0`, side `1`, the head of side `2`, and the cut.
The count `m + 2` agrees with the descent bound at its smallest admissible
input. -/
theorem innerCut_quadrilateral_sideCount : (2 : ℕ) + 2 = 4 := rfl

end Estimating
end VanKampen
end GGT
end GroupApproximation
