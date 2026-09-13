import GroupApproximation.GGT.VanKampen.Estimating.UnboundPolygonCut
import GroupApproximation.Meta.AxiomGuard

/-!
# First-visit witnesses along a side of a closed geodesic polygon

`exists_close_other_side` puts every point of side `b` of a closed geodesic
`n`-gon within `3δ(c+1)` of one of the other sides. The witness is chosen
existentially, so the witnesses of two points of side `b` are unrelated, and
`exists_long_close_pair` ends with `β ≤ |s' - s|`: the two fellow-travelling
segments may run in either relative direction.

Planar surgery on a van Kampen diagram contradicts only the antiparallel case,
in which the boundary loop reads the two segments in opposite directions. This
module supplies witnesses that are monotone along side `b`, which is what
produces that orientation.

**First-visit witnesses** (`exists_firstVisit_witnesses`). Read side `b`
backwards from `vs (b + 1)` at parameter `r`, and read the other sides forwards
in their order around the polygon. Among all `3δ(c+1)`-close points on the
other sides, take the least side index and, on that side, the least parameter.
The close parameters on a side form a closed set (`isClosed_closeParameters`),
so the least parameter is attained (`exists_least_closeParameter`).

**Monotonicity** (`exists_close_prefix_side`). Let `(j', s')` be a witness for
`r'`. Cut the polygon along a geodesic from the witness point to the point `r'`
of side `b`. The inner piece has `j' + 3` sides: the part of side `b` from `r'`
to `vs (b + 1)`, the sides `b + 1, …, b + j'`, side `b + 1 + j'` up to `s'`, and
the cut, of length at most `3δ(c+1)`. By the chord lemma on this piece, each
point `r ≤ r'` lies within `3δ(c+1)` of one of its other sides. If that side is
the cut, then `r' - r ≤ 6δ(c+1)`. Otherwise the point found is a witness for `r`
in the original polygon, lexicographically at most `(j', s')`. So first-visit
witnesses are lexicographically monotone in `r` once `r' - r > 6δ(c+1)`,
provided `n ≤ 2 ^ c`, which bounds the piece.
-/

namespace GroupApproximation
namespace Olshanskii

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.VanKampen.Estimating

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-- The parameters of a geodesic segment at distance at most `D` from a fixed
point form a closed set. -/
theorem isClosed_closeParameters {f : ℝ → X} {M D : ℝ}
    (h : IsGeodesicSegment f 0 M) (x : X) :
    IsClosed {s : ℝ | s ∈ Set.Icc (0 : ℝ) M ∧ dist x (f s) ≤ D} := by
  have hcont : ContinuousOn (fun s => dist x (f s)) (Set.Icc (0 : ℝ) M) := by
    rw [Metric.continuousOn_iff]
    intro a ha ε hε
    refine ⟨ε, hε, fun a' ha' hlt => ?_⟩
    show dist (dist x (f a')) (dist x (f a)) < ε
    have h1 : dist (f a') (f a) = |a' - a| := h a' ha' a ha
    have h2 := abs_dist_sub_le (f a') (f a) x
    rw [Real.dist_eq] at hlt ⊢
    rw [dist_comm x (f a'), dist_comm x (f a)]
    linarith
  have hcl : IsClosed (Set.Icc (0 : ℝ) M ∩ (fun s => dist x (f s)) ⁻¹' Set.Iic D) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  exact hcl

/-- If some parameter of a geodesic segment is `D`-close to a point, then a
least such parameter exists. -/
theorem exists_least_closeParameter {f : ℝ → X} {M D : ℝ}
    (h : IsGeodesicSegment f 0 M) (x : X) {s0 : ℝ}
    (hs0 : s0 ∈ Set.Icc (0 : ℝ) M) (hd0 : dist x (f s0) ≤ D) :
    ∃ s ∈ Set.Icc (0 : ℝ) M, dist x (f s) ≤ D ∧
      ∀ s' ∈ Set.Icc (0 : ℝ) M, dist x (f s') ≤ D → s ≤ s' := by
  have hcl := isClosed_closeParameters (D := D) h x
  have hne : {s : ℝ | s ∈ Set.Icc (0 : ℝ) M ∧ dist x (f s) ≤ D}.Nonempty :=
    ⟨s0, hs0, hd0⟩
  have hbdd : BddBelow {s : ℝ | s ∈ Set.Icc (0 : ℝ) M ∧ dist x (f s) ≤ D} :=
    ⟨0, fun _ hs => hs.1.1⟩
  have hmem := hcl.csInf_mem hne hbdd
  exact ⟨_, hmem.1, hmem.2, fun s' hs' hd' => csInf_le hbdd ⟨hs', hd'⟩⟩

/-- **First-visit witnesses.** In a closed geodesic `n`-gon read from `b`, with
`n - 1 ≤ 2 ^ c`, every point `r` of side `b`, read backwards from `vs (b + 1)`,
has a witness `(jf r, sf r)`: a point of side `b + 1 + jf r` at parameter
`sf r` within `3δ(c+1)` of it. The witness is lexicographically least among
all such points. -/
theorem exists_firstVisit_witnesses {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n c b : ℕ} (hn : 2 ≤ n) (hc : n - 1 ≤ 2 ^ c)
    {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides b n) :
    ∃ jf : ℝ → ℕ, ∃ sf : ℝ → ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))),
        jf t < n - 1 ∧
          sf t ∈ Set.Icc (0 : ℝ)
            (dist (vs (b + 1 + jf t)) (vs (b + 1 + jf t + 1))) ∧
          dist (sides b (dist (vs b) (vs (b + 1)) - t))
              (sides (b + 1 + jf t) (sf t)) ≤ 3 * δ * ((c : ℝ) + 1) ∧
          ∀ j < n - 1, ∀ s ∈ Set.Icc (0 : ℝ)
              (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))),
            dist (sides b (dist (vs b) (vs (b + 1)) - t)) (sides (b + 1 + j) s)
                ≤ 3 * δ * ((c : ℝ) + 1) →
              jf t < j ∨ (jf t = j ∧ sf t ≤ s) := by
  classical
  have hall : ∀ t : ℝ, ∃ j : ℕ, ∃ s : ℝ,
      t ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1))) →
        j < n - 1 ∧
          s ∈ Set.Icc (0 : ℝ) (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))) ∧
          dist (sides b (dist (vs b) (vs (b + 1)) - t)) (sides (b + 1 + j) s)
              ≤ 3 * δ * ((c : ℝ) + 1) ∧
          ∀ j' < n - 1, ∀ s' ∈ Set.Icc (0 : ℝ)
              (dist (vs (b + 1 + j')) (vs (b + 1 + j' + 1))),
            dist (sides b (dist (vs b) (vs (b + 1)) - t)) (sides (b + 1 + j') s')
                ≤ 3 * δ * ((c : ℝ) + 1) →
              j < j' ∨ (j = j' ∧ s ≤ s') := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) (dist (vs b) (vs (b + 1)))
    · have hex : ∃ j : ℕ, j < n - 1 ∧ ∃ s ∈ Set.Icc (0 : ℝ)
            (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))),
          dist (sides b (dist (vs b) (vs (b + 1)) - t)) (sides (b + 1 + j) s)
            ≤ 3 * δ * ((c : ℝ) + 1) :=
        exists_close_other_side hδ hδ0 hgeo hn hc hpoly ht
      obtain ⟨hj, s0, hs0, hd0⟩ := Nat.find_spec hex
      obtain ⟨hgj, -, -⟩ := hpoly.1 (b + 1 + Nat.find hex) (by omega) (by omega)
      obtain ⟨s1, hs1, hd1, hmin1⟩ := exists_least_closeParameter hgj _ hs0 hd0
      refine ⟨Nat.find hex, s1, fun _ => ⟨hj, hs1, hd1, ?_⟩⟩
      intro j' hj' s' hs' hd'
      have hle : Nat.find hex ≤ j' := Nat.find_min' hex ⟨hj', s', hs', hd'⟩
      by_cases hlt : Nat.find hex < j'
      · exact Or.inl hlt
      · have heq : Nat.find hex = j' := by omega
        refine Or.inr ⟨heq, ?_⟩
        rw [← heq] at hs' hd'
        exact hmin1 s' hs' hd'
    · exact ⟨0, 0, fun h => absurd h ht⟩
  choose jf sf hjs using hall
  exact ⟨jf, sf, hjs⟩

/-- **The prefix chord.** Let `(j', s')` be a `3δ(c+1)`-close point for the
parameter `r'` of side `b`, read backwards, with `n ≤ 2 ^ c`. Every parameter
`r ≤ r'` with `r' - r > 6δ(c+1)` has a `3δ(c+1)`-close point `(j, s)` that is
lexicographically at most `(j', s')`. -/
theorem exists_close_prefix_side {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n c b : ℕ} (hc : n ≤ 2 ^ c)
    {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides b n)
    {r r' : ℝ} (hr0 : 0 ≤ r) (hr' : r' ≤ dist (vs b) (vs (b + 1)))
    (hgap : 2 * (3 * δ * ((c : ℝ) + 1)) < r' - r)
    {j' : ℕ} (hj' : j' < n - 1) {s' : ℝ}
    (hs' : s' ∈ Set.Icc (0 : ℝ) (dist (vs (b + 1 + j')) (vs (b + 1 + j' + 1))))
    (hd' : dist (sides b (dist (vs b) (vs (b + 1)) - r')) (sides (b + 1 + j') s')
      ≤ 3 * δ * ((c : ℝ) + 1)) :
    ∃ j < n - 1, ∃ s ∈ Set.Icc (0 : ℝ) (dist (vs (b + 1 + j)) (vs (b + 1 + j + 1))),
      dist (sides b (dist (vs b) (vs (b + 1)) - r)) (sides (b + 1 + j) s)
          ≤ 3 * δ * ((c : ℝ) + 1) ∧
        (j < j' ∨ (j = j' ∧ s ≤ s')) := by
  have hbn : b < b + n := by omega
  obtain ⟨hb, -, -⟩ := hpoly.1 b (le_refl b) hbn
  have hcast0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hD0 : (0 : ℝ) ≤ 3 * δ * ((c : ℝ) + 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hidx : b + (j' + 1) = b + 1 + j' := by omega
  have hs'le : s' ≤ dist (vs (b + (j' + 1))) (vs (b + (j' + 1) + 1)) := by
    rw [hidx]
    exact hs'.2
  -- the cut from the witness point back to side `b`
  obtain ⟨cut, hcut, hcut0, hcut1⟩ :=
    hgeo (sides (b + (j' + 1)) s') (sides b (dist (vs b) (vs (b + 1)) - r'))
  obtain ⟨hQ, hQ0, hQmid, hQend, hQcut⟩ :=
    exists_innerCut_polygon (a := b) (m := j' + 1)
      (s := dist (vs b) (vs (b + 1)) - r') (s' := s') (cut := cut) hpoly (le_refl b)
      (by omega) (by omega) (by linarith) (by linarith) hs'.1 hs'le hcut hcut0 hcut1
  -- the chord lemma on the inner piece
  have htQ : r ∈ Set.Icc (0 : ℝ)
      (dist (innerVertex vs sides b (j' + 1) (dist (vs b) (vs (b + 1)) - r') s' 0)
        (innerVertex vs sides b (j' + 1) (dist (vs b) (vs (b + 1)) - r') s' (0 + 1))) := by
    rw [zero_add, hQ0]
    exact ⟨hr0, by linarith⟩
  obtain ⟨j, hj, s, hs, hd⟩ :=
    exists_close_other_side hδ hδ0 hgeo (n := j' + 1 + 2) (c := c) (b := 0)
      (by omega) (le_trans (by omega) hc) hQ htQ
  have hleft : innerSide sides b (j' + 1) (dist (vs b) (vs (b + 1)) - r') cut 0
      (dist (innerVertex vs sides b (j' + 1) (dist (vs b) (vs (b + 1)) - r') s' 0)
        (innerVertex vs sides b (j' + 1) (dist (vs b) (vs (b + 1)) - r') s' (0 + 1))
        - r) = sides b (dist (vs b) (vs (b + 1)) - r) := by
    rw [zero_add, hQ0, innerSide_zero]
    refine congrArg (sides b) ?_
    ring
  rw [hleft] at hd
  have hj1 : 0 + 1 + j = j + 1 := by omega
  rw [hj1] at hs hd
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · -- an untouched side before `b + 1 + j'`
    rw [innerSide_mid (j := j + 1) sides b (j' + 1) (dist (vs b) (vs (b + 1)) - r') cut
      (by omega) (by omega)] at hd
    rw [hQmid (j + 1) (by omega) (by omega)] at hs
    have harg : b + (j + 1) = b + 1 + j := by omega
    rw [harg] at hs hd
    exact ⟨j, by omega, s, hs, hd, Or.inl hlt⟩
  · -- the head of side `b + 1 + j'`, up to `s'`
    rw [heq] at hs hd
    rw [innerSide_end sides b (j' + 1) (dist (vs b) (vs (b + 1)) - r') cut
      (by omega)] at hd
    rw [hQend] at hs
    rw [hidx] at hd
    exact ⟨j', hj', s, ⟨hs.1, le_trans hs.2 hs'.2⟩, hd, Or.inr ⟨rfl, hs.2⟩⟩
  · -- the cut: then `r` and `r'` are `6δ(c+1)`-close, against the gap
    exfalso
    have hjj : j = j' + 1 := by omega
    rw [hjj] at hs hd
    rw [innerSide_cut] at hd
    rw [show j' + 1 + 1 + 1 = j' + 1 + 2 from by omega, hQcut] at hs
    have hlen : dist (sides (b + (j' + 1)) s') (sides b (dist (vs b) (vs (b + 1)) - r'))
        ≤ 3 * δ * ((c : ℝ) + 1) := by
      rw [hidx, dist_comm]
      exact hd'
    have hcs : dist (cut s) (cut (dist (sides (b + (j' + 1)) s')
        (sides b (dist (vs b) (vs (b + 1)) - r')))) =
        dist (sides (b + (j' + 1)) s') (sides b (dist (vs b) (vs (b + 1)) - r')) - s := by
      rw [hcut s hs (dist (sides (b + (j' + 1)) s') (sides b (dist (vs b) (vs (b + 1)) - r')))
          ⟨dist_nonneg, le_refl _⟩,
        abs_of_nonpos (show s - dist (sides (b + (j' + 1)) s')
          (sides b (dist (vs b) (vs (b + 1)) - r')) ≤ 0 by linarith [hs.2])]
      ring
    rw [hcut1] at hcs
    have hspan : dist (sides b (dist (vs b) (vs (b + 1)) - r))
        (sides b (dist (vs b) (vs (b + 1)) - r')) = r' - r := by
      rw [hb (dist (vs b) (vs (b + 1)) - r) ⟨by linarith, by linarith⟩
          (dist (vs b) (vs (b + 1)) - r') ⟨by linarith, by linarith⟩,
        abs_of_nonneg (show (0 : ℝ) ≤ dist (vs b) (vs (b + 1)) - r
          - (dist (vs b) (vs (b + 1)) - r') by linarith)]
      ring
    have htri := dist_triangle (sides b (dist (vs b) (vs (b + 1)) - r)) (cut s)
      (sides b (dist (vs b) (vs (b + 1)) - r'))
    linarith [hs.1]

#audit_axioms GroupApproximation.Olshanskii.isClosed_closeParameters
#audit_axioms GroupApproximation.Olshanskii.exists_least_closeParameter
#audit_axioms GroupApproximation.Olshanskii.exists_firstVisit_witnesses
#audit_axioms GroupApproximation.Olshanskii.exists_close_prefix_side

end Olshanskii
end GroupApproximation
