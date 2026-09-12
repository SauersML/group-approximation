import GroupApproximation.GGT.OsinTheorem54SepGeodesicSides
import GroupApproximation.GGT.OsinTheorem54SepCommIndex

/-!
# The geodesic triangle, as a polygon

Osin's Lemma 4.5 compares a geodesic `f → g` with a path made of two geodesic
segments `f → h → g`, and the comparison is made inside the polygon those three
paths bound.  This module builds that polygon.

It is the quadrilateral with an empty first side, `[] ++ u ++ revWord x ++
revWord v`, which is definitionally `u ++ revWord x ++ revWord v`; the cut
function, the side clause and the component transfers are the ones already in
the tree.  The cost of carrying a triangle as a degenerate quadrilateral is that
the isolated-component bound arrives at `n = 4` rather than `3`, so where Osin
writes `D ≥ 3C` this development will want `4C ≤ D`.  That costs nothing: `D` is
chosen by the assembly AFTER `C` is in hand, so a larger lower bound is still a
choice and not a hypothesis.

## Basepoints

`sepSet` is stated at the basepoint `f`, and the polygon lemmas so far are
stated at `1`, so the predicate has to move.  It moves for free:
`IsQuasiGeodesicPolygon` mentions its basepoint only through distances between
vertices, and both the vertex map and the word metric are left-invariant.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The polygon predicate is basepoint-free.**  Left translation carries the
path read from `1` to the path read from `v`, and the word metric does not
notice. -/
theorem isQuasiGeodesicPolygon_translate (D : RelGenSet G Λ) {mu b : ℝ} {n : ℕ}
    (v : G) {ws : List (RelLetter G Λ)}
    (h : IsQuasiGeodesicPolygon D mu b n 1 ws) :
    IsQuasiGeodesicPolygon D mu b n v ws := by
  obtain ⟨hlet, hclosed, c, hc0, hcn, hcmono, hcqg⟩ := h
  refine ⟨hlet, hclosed, c, hc0, hcn, hcmono, ?_⟩
  intro s hs i j hi hij hj
  have hq := hcqg s hs i j hi hij hj
  rw [vertex_eq_mul_vertex_one ws v i, vertex_eq_mul_vertex_one ws v j,
    wordDist_left_invariant]
  exact hq

/-- **A geodesic word read from its own basepoint.**  `IsGeodesicWord D f g u`
and `IsGeodesicWord D 1 (listVal u) u` say the same thing: the second field
identifies `f⁻¹g` with `listVal u`, and the word metric is left-invariant. -/
theorem isGeodesicWord_one_of (D : RelGenSet G Λ) {f g : G}
    {u : List (RelLetter G Λ)} (hu : IsGeodesicWord D f g u) :
    IsGeodesicWord D 1 (RelLetter.listVal u) u := by
  refine ⟨hu.1, one_mul _, ?_⟩
  have hval : RelLetter.listVal u = f⁻¹ * g := by
    rw [← hu.2.1]
    group
  have hd : wordDist D.alphabet.carrier 1 (RelLetter.listVal u)
      = wordDist D.alphabet.carrier f g := by
    rw [hval]
    show wordNorm D.alphabet.carrier (1⁻¹ * (f⁻¹ * g))
      = wordNorm D.alphabet.carrier (f⁻¹ * g)
    rw [inv_one, one_mul]
  rw [hd]
  exact hu.2.2

/-- **The geodesic triangle `f → g`, `f → h`, `h → g` is a `(1,0)`-quasi-geodesic
polygon**, read from `f`, carried as a quadrilateral whose first side is empty.

The two-segment path of Osin's Lemma 4.5 is `v` followed by `x`; the third side
is the geodesic `u` the separating coset is witnessed on. -/
theorem isQuasiGeodesicPolygon_triangle (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {f g h : G}
    {u v x : List (RelLetter G Λ)} (hu : IsGeodesicWord D f g u)
    (hv : IsGeodesicWord D f h v) (hx : IsGeodesicWord D h g x) :
    IsQuasiGeodesicPolygon D 1 0 4 f (u ++ revWord x ++ revWord v) := by
  refine isQuasiGeodesicPolygon_translate D f ?_
  have hxrev : IsGeodesicWord D g h (revWord x) :=
    isGeodesicWord_revWord D hsymm hx
  have hclose : RelLetter.listVal v
      = RelLetter.listVal ([] : List (RelLetter G Λ)) * RelLetter.listVal u
        * RelLetter.listVal (revWord x) := by
    have hvval : RelLetter.listVal v = f⁻¹ * h := by
      rw [← hv.2.1]
      group
    have huval : RelLetter.listVal u = f⁻¹ * g := by
      rw [← hu.2.1]
      group
    have hxval : RelLetter.listVal (revWord x) = g⁻¹ * h := by
      rw [← hxrev.2.1]
      group
    rw [hvval, huval, hxval, RelLetter.listVal_nil, one_mul]
    group
  exact isQuasiGeodesicPolygon_fourGon_of_geodesic D hsymm [] u (revWord x) v
    ⟨by simp, one_mul _, by
        rw [List.length_nil, RelLetter.listVal_nil]
        show 0 = wordNorm D.alphabet.carrier (1⁻¹ * 1)
        rw [inv_one, one_mul, wordNorm_one]⟩
    (isGeodesicWord_one_of D hu) (isGeodesicWord_one_of D hxrev)
    (isGeodesicWord_one_of D hv) hclose

end OsinComponents
end GGT
end GroupApproximation
