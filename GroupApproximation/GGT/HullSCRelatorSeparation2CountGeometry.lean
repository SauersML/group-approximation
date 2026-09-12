import GroupApproximation.GGT.HullSCRelatorSeparation2CountBigon
import GroupApproximation.GGT.HullEeUniformCut
import GroupApproximation.GGT.DGOPolygonSideCountAll

/-!
# The geometric block count at a fixed producer length

The count in `HullSCRelatorSeparation2CountBigon` needs an isolated-component
bound for the closed figure `u ++ revWord q`.  Treating that figure as a
two-gon would be circular: the near side `u` is precisely the word whose
quasi-geodesicity the count is meant to prove.

There is no circle if every edge is made a side.  A side of length at most one
is `(1,1)`-quasi-geodesic without any non-triviality assumption, so a closed
figure of length at most `N` is an `N`-gon.  The explicit `N`-gon estimate then
puts every isolated component in the ball

`(N + 1) * (25 * (delta + 2)) * (N + 2)`.

Consequently, once the producer fixes an upper bound `N` for the figure and
chooses every relator component outside that one ball, all counted components
cross to the geodesic side and the combinatorial injection gives the count
with no error term.  In the intended application a segment has length at most
the fixed relator target and its geodesic chord is no longer than the segment,
so `N` may be twice that target.  In particular the radius is fixed before the
exact exponent list is chosen and does not grow with that list.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u v

section CountGeometry

variable {G : Type u} [Group G] {Lambda : Type v}

/-- The isolated-component radius for an every-edge `N`-gon at additive
constant one. -/
def everyEdgeIsolationRadius (delta N : ℕ) : ℕ :=
  (N + 1) * (25 * (delta + 2)) * (N + 2)

/-- **Uniform isolation bound for a bounded closed figure.**

No side of the figure is assumed quasi-geodesic.  Instead every edge is a
side, and the length bound pads the cut with empty sides up to the fixed count
`N`.  This is the non-circular isolated-component input needed by the relator
count. -/
theorem isolatedComponent_mem_relBall_of_closed_length_le
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {delta N : ℕ} (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (v : G) {w : List (RelLetter G Lambda)}
    (hletters : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) (hlength : w.length ≤ N)
    {lam : Lambda} {i k : ℕ} (hcomp : IsComp lam w i k)
    (hisolated : IsIsolated D.fam lam v w i) :
    (vertex v w i)⁻¹ * vertex v w k ∈
      D.relBall lam (everyEdgeIsolationRadius delta N) := by
  have hpolygon : IsQuasiGeodesicPolygon D 1 ((1 : ℕ) : ℝ) N v w :=
    isQuasiGeodesicPolygon_everyEdge D 1 le_rfl v hletters hclosed hlength
  exact isolatedComponentBound_nGon_of_fourPointHyperbolic
    D hsymm 1 hdelta N v w hpolygon lam i k hcomp hisolated

/-- **The fixed-length geometric injection count.**

The figure is `u ++ revWord q`, but its near side is not required to be
quasi-geodesic.  A uniform bound on the total figure length supplies the
isolated-component estimate edge by edge.  Components deeper than that bound
are therefore non-isolated; same-side separation sends them across to `q`, and
the injection of `card_le_card_of_deep` proves the count.

The conclusion has no additive exception.  All constants occur only in the
single threshold comparison `everyEdgeIsolationRadius delta N ≤ rho`, so a
producer fixing `N` can choose its exact relator data afterward. -/
theorem card_le_card_of_boundedClosedBigon
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {delta N : ℕ} (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lam : Lambda) (v : G) (u q : List (RelLetter G Lambda))
    (S Q : Finset ℕ) {rho : ℕ}
    (hletters : ∀ a ∈ u ++ revWord q, D.IsLetter a)
    (hclosed : RelLetter.listVal (u ++ revWord q) = 1)
    (hlength : (u ++ revWord q).length ≤ N)
    (hrho : everyEdgeIsolationRadius delta N ≤ rho)
    (hSu : ∀ x ∈ S, x < u.length)
    (hScomp : ∀ x ∈ S, ∃ k : ℕ,
      IsComp lam (u ++ revWord q) x k ∧
        (vertex v (u ++ revWord q) x)⁻¹ * vertex v (u ++ revWord q) k
          ∉ D.relBall lam rho)
    (hsep : ∀ x : ℕ, x < u.length → ∀ y : ℕ, y < u.length → x ≠ y →
      IsCompStart lam (u ++ revWord q) x →
      IsCompStart lam (u ++ revWord q) y →
      ¬ Connected D.fam lam v (u ++ revWord q) x y)
    (hQ : ∀ y : ℕ, y < q.length →
      IsCompStart lam (u ++ revWord q) (u.length + y) → y ∈ Q) :
    S.card ≤ Q.card := by
  refine card_le_card_of_deep D lam v u q S Q
    (R := everyEdgeIsolationRadius delta N) (rho := rho) ?_ hrho hSu hScomp hsep hQ
  intro i k hcomp hisolated
  exact isolatedComponent_mem_relBall_of_closed_length_le
    D hsymm hdelta v hletters hclosed hlength hcomp hisolated

/-- **The bounded geodesic-bigon injection, with closure and length derived.**

If `u` has length at most the fixed producer target `L`, a geodesic chord with
the same endpoints has length at most `u.length`.  Hence
`u ++ revWord q` has length at most `2 * L`, closes, and is covered by the
every-edge isolation radius at `2 * L`.  This is the application-facing form:
neither closure nor a bound involving the eventually chosen exponent list is
an input. -/
theorem card_le_card_of_boundedGeodesicBigon
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {delta L : ℕ} (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lam : Lambda) (v : G) (u q : List (RelLetter G Lambda))
    (S Q : Finset ℕ) {rho : ℕ}
    (huletters : ∀ a ∈ u, D.IsLetter a)
    (hq : IsGeodesicWord D v (vertex v u u.length) q)
    (hulength : u.length ≤ L)
    (hrho : everyEdgeIsolationRadius delta (2 * L) ≤ rho)
    (hSu : ∀ x ∈ S, x < u.length)
    (hScomp : ∀ x ∈ S, ∃ k : ℕ,
      IsComp lam (u ++ revWord q) x k ∧
        (vertex v (u ++ revWord q) x)⁻¹ * vertex v (u ++ revWord q) k
          ∉ D.relBall lam rho)
    (hsep : ∀ x : ℕ, x < u.length → ∀ y : ℕ, y < u.length → x ≠ y →
      IsCompStart lam (u ++ revWord q) x →
      IsCompStart lam (u ++ revWord q) y →
      ¬ Connected D.fam lam v (u ++ revWord q) x y)
    (hQ : ∀ y : ℕ, y < q.length →
      IsCompStart lam (u ++ revWord q) (u.length + y) → y ∈ Q) :
    S.card ≤ Q.card := by
  have hqval : RelLetter.listVal q = RelLetter.listVal u := by
    apply mul_left_cancel (a := v)
    rw [← vertex_length v u]
    exact hq.2.1
  have hclosed : RelLetter.listVal (u ++ revWord q) = 1 := by
    rw [listVal_append, listVal_revWord, hqval, mul_inv_cancel]
  have hletters : ∀ a ∈ u ++ revWord q, D.IsLetter a := by
    intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · exact huletters a ha
    · exact isLetter_of_mem_revWord D hsymm hq.1 a ha
  have hdist : wordDist D.alphabet.carrier v (vertex v u u.length) ≤ u.length := by
    have hraw := wordDist_vertex_le' D huletters v (i := 0) (j := u.length)
      (Nat.zero_le _) (le_refl _)
    rw [vertex_zero] at hraw
    omega
  have hqlength : q.length ≤ u.length := by
    rw [hq.2.2]
    exact hdist
  have hfigureLength : (u ++ revWord q).length ≤ 2 * L := by
    rw [List.length_append, length_revWord]
    omega
  exact card_le_card_of_boundedClosedBigon D hsymm hdelta lam v u q S Q
    hletters hclosed hfigureLength hrho hSu hScomp hsep hQ

end CountGeometry

end OsinComponents
end GGT
end GroupApproximation
