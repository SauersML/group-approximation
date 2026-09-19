import GroupApproximation.GGT.VanKampen.Estimating.UnboundPolygonCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Classes and inherited long pairs in geodesic polygons

A long pair records actual parameters on two sides. Translating those
parameters lifts a pair from restricted sides, without shortening either
segment. Re-reading a polygon preserves its class lengths and distinct side
indices, including at the closing vertex.
-/

namespace GroupApproximation.Olshanskii

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.VanKampen.Estimating
open Finset

universe v
variable {X : Type v} [PseudoMetricSpace X]

/-- Two subsegments with long parameter intervals and close corresponding
endpoints. Orientation on either side is immaterial. -/
def SidePair (vs : ℕ → X) (sides : ℕ → ℝ → X) (i j : ℕ) (β D : ℝ) : Prop :=
  ∃ u ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
    ∃ u' ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
      ∃ t ∈ Set.Icc (0 : ℝ) (dist (vs j) (vs (j + 1))),
        ∃ t' ∈ Set.Icc (0 : ℝ) (dist (vs j) (vs (j + 1))),
          β ≤ |u' - u| ∧ β ≤ |t' - t| ∧
            dist (sides i u) (sides j t) ≤ D ∧
            dist (sides i u') (sides j t') ≤ D

/-- The first side belongs to `A`, the other to `B`, and they are distinct. -/
def ClassPair (vs : ℕ → X) (sides : ℕ → ℝ → X) (n : ℕ)
    (A B : Set ℕ) (β D : ℝ) : Prop :=
  ∃ i < n, ∃ j < n, i ∈ A ∧ j ∈ B ∧ i ≠ j ∧ SidePair vs sides i j β D

/-- Total length of one class of sides. -/
noncomputable def classLength (vs : ℕ → X) (n : ℕ) (A : Set ℕ) : ℝ :=
  by
    classical
    exact ∑ i ∈ range n, if i ∈ A then dist (vs i) (vs (i + 1)) else 0

theorem classLength_nonneg (vs : ℕ → X) (n : ℕ) (A : Set ℕ) :
    0 ≤ classLength vs n A := by
  classical
  unfold classLength
  exact sum_nonneg fun i _ => by split_ifs <;> positivity

/-- A pair on restrictions lifts by translating both parameter intervals. -/
theorem SidePair.of_restrictions
    {v w : ℕ → X} {p q : ℕ → ℝ → X} {i j a b : ℕ} {β D s t : ℝ}
    (h : SidePair v p i j β D)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hi : s + dist (v i) (v (i + 1)) ≤ dist (w a) (w (a + 1)))
    (hj : t + dist (v j) (v (j + 1)) ≤ dist (w b) (w (b + 1)))
    (hp : ∀ r ∈ Set.Icc (0 : ℝ) (dist (v i) (v (i + 1))), p i r = q a (s + r))
    (hq : ∀ r ∈ Set.Icc (0 : ℝ) (dist (v j) (v (j + 1))), p j r = q b (t + r)) :
    SidePair w q a b β D := by
  obtain ⟨u, hu, u', hu', r, hr, r', hr', hlen, hlen', hclose, hclose'⟩ := h
  refine ⟨s + u, ⟨by linarith [hu.1], by linarith [hu.2]⟩,
    s + u', ⟨by linarith [hu'.1], by linarith [hu'.2]⟩,
    t + r, ⟨by linarith [hr.1], by linarith [hr.2]⟩,
    t + r', ⟨by linarith [hr'.1], by linarith [hr'.2]⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [add_sub_add_left_eq_sub] using hlen
  · simpa only [add_sub_add_left_eq_sub] using hlen'
  · simpa only [hp u hu, hq r hr] using hclose
  · simpa only [hp u' hu', hq r' hr'] using hclose'

/-- The side index after passing through the closing vertex once. -/
def wrapSide (n i : ℕ) : ℕ := if i < n then i else i - n

theorem wrapSide_lt {n k i : ℕ} (hk : k < n) (hi : i < k + n) :
    wrapSide n i < n := by
  unfold wrapSide
  split_ifs <;> omega

theorem wrapSide_injective {n k i j : ℕ}
    (hi0 : k ≤ i) (hi1 : i < k + n) (hj0 : k ≤ j) (hj1 : j < k + n)
    (h : wrapSide n i = wrapSide n j) : i = j := by
  unfold wrapSide at h
  split_ifs at h <;> omega

omit [PseudoMetricSpace X] in
theorem rotSide_eq_wrap (sides : ℕ → ℝ → X) (n i : ℕ) :
    rotSide sides n 0 i = sides (wrapSide n i) := by
  simp only [rotSide, wrapSide, zero_add]
  split_ifs <;> rfl

theorem rotVertex_dist_eq_wrap {vs : ℕ → X} {n : ℕ}
    (hclose : vs n = vs 0) (i : ℕ) :
    dist (rotVertex vs n 0 i) (rotVertex vs n 0 (i + 1)) =
      dist (vs (wrapSide n i)) (vs (wrapSide n i + 1)) := by
  rcases lt_trichotomy i n with hi | hi | hi
  · simp only [rotVertex, wrapSide, zero_add, if_pos hi,
      if_pos (show i ≤ n by omega), if_pos (show i + 1 ≤ n by omega)]
  · subst i
    simp [rotVertex, wrapSide, hclose]
  · simp only [rotVertex, wrapSide, zero_add, if_neg (show ¬ i < n by omega),
      if_neg (show ¬ i ≤ n by omega), if_neg (show ¬ i + 1 ≤ n by omega),
      show i + 1 - n = i - n + 1 by omega]

theorem SidePair.of_rotation {vs : ℕ → X} {sides : ℕ → ℝ → X}
    {n i j : ℕ} {β D : ℝ} (hclose : vs n = vs 0)
    (h : SidePair (rotVertex vs n 0) (rotSide sides n 0) i j β D) :
    SidePair vs sides (wrapSide n i) (wrapSide n j) β D := by
  apply h.of_restrictions (s := 0) (t := 0) (by norm_num) (by norm_num)
  · simp only [zero_add, rotVertex_dist_eq_wrap hclose, le_refl]
  · simp only [zero_add, rotVertex_dist_eq_wrap hclose, le_refl]
  · intro r _
    simp only [rotSide_eq_wrap, zero_add]
  · intro r _
    simp only [rotSide_eq_wrap, zero_add]

/-- A cyclic shift permutes all side weights, not just their support. -/
theorem sum_wrapSide (f : ℕ → ℝ) {n k : ℕ} (hk : k ≤ n) :
    (∑ j ∈ range n, f (wrapSide n (k + j))) = ∑ j ∈ range n, f j := by
  have hn : n = (n - k) + k := by omega
  have hfirst : (∑ j ∈ range (n - k), f (wrapSide n (k + j))) =
      ∑ j ∈ range (n - k), f (k + j) := by
    apply sum_congr rfl
    intro j hj
    have hjn := mem_range.mp hj
    simp only [wrapSide, if_pos (show k + j < n by omega)]
  have hsecond : (∑ j ∈ range k, f (wrapSide n (k + (n - k + j)))) =
      ∑ j ∈ range k, f j := by
    apply sum_congr rfl
    intro j _
    simp only [wrapSide, if_neg (show ¬ k + (n - k + j) < n by omega),
      show k + (n - k + j) - n = j by omega]
  calc
    (∑ j ∈ range n, f (wrapSide n (k + j))) =
        (∑ j ∈ range (n - k), f (wrapSide n (k + j))) +
        ∑ j ∈ range k, f (wrapSide n (k + (n - k + j))) := by
      simpa only [← hn] using sum_range_add (fun j => f (wrapSide n (k + j))) (n - k) k
    _ = (∑ j ∈ range (n - k), f (k + j)) + ∑ j ∈ range k, f j := by
      rw [hfirst, hsecond]
    _ = ∑ j ∈ range n, f j := by
      have h := sum_range_add f k (n - k)
      rw [show k + (n - k) = n by omega] at h
      rw [h]
      exact add_comm _ _

end GroupApproximation.Olshanskii

#audit_axioms GroupApproximation.Olshanskii.SidePair.of_restrictions
#audit_axioms GroupApproximation.Olshanskii.SidePair.of_rotation
#audit_axioms GroupApproximation.Olshanskii.sum_wrapSide
