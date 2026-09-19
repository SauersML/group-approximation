import GroupApproximation.GGT.DGOThinPolygonVertex
import GroupApproximation.GGT.HullSCConeOffHeavyHyperbolic

/-!
# Quasiconvexity transports across a bounded Hausdorff distance

`GGT/HullSCConeOffHeavyQuasiconvex.lean` proves `IsWordQuasiconvex` for the
cyclic subgroup `⟨g⟩` of a loxodromic element.  The family the cone-off leaf
actually needs is the elementary closure `E(g)` — `GGT/HullSCConeOffHeavyProperPower.lean`
shows that a cyclic subgroup properly contained in its elementary closure fails
clause (b) outright — and `⟨g⟩` sits inside `E(g)` with bounded Hausdorff
distance, since it has finite index there.

This module makes that passage a theorem: quasiconvexity of a subgroup transports
to any larger subgroup lying within a bounded neighbourhood of it, at the cost of
`2D + 4δ` in the constant.

## The mechanism

Two facts, each one application of the four-point condition.

* `exists_isBetween_near_of_endpoint_close`: moving one endpoint by `D` moves the
  geodesic by at most `2D + 2δ`.  Given `p` between `x` and `b`, the point `q`
  between `x` and `b'` at parameter `min (d(x,p)) (d(x,b'))` is within
  `2D + 2δ` of `p`.  Both competing pairings of the four-point condition at
  `(x, b', p, q)` are at most `d(x,b') + 2D`, whichever side of the minimum the
  parameter falls on.
* `GGT.wordDist_le_two_mul_of_isBetween`: two between-points at the same
  parameter are `2δ` apart, which is what lets an abstract between-point of
  `(1,b')` be replaced by an honest prefix of a geodesic word for `b'` — the
  object `IsWordQuasiconvex` quantifies over.

Chaining them: a prefix `p` of a geodesic word for `b ∈ H` is `2D + 2δ` from a
between-point `q` of `(1, b')` for the nearby `b' ∈ H'`, which is `2δ` from a
prefix of a geodesic word for `b'`, which is `σ` from `H'` — and `H' ≤ H`.

## What is not proved here

That `⟨g⟩` really is at bounded Hausdorff distance from `E(g)`.  That is
Dahmani--Guirardel--Osin's Lemma 6.5, whose honest leaf in this repository is
`GGT.Elementary.ElementaryClosureCoarseTranslation`
(`GGT/ElementaryProjectionCriterion.lean`), and it is left as the hypothesis
`hclose` rather than assumed silently.  Stating it as a hypothesis is also what
keeps this lemma general: nothing here is about elementary closures.

## Model tests

At `H' = H` and `D = 0` the statement is `IsWordQuasiconvex A H σ →
IsWordQuasiconvex A H (σ + 4δ)`, a weakening, so nothing is manufactured.  At
`H' = ⊥` the hypothesis `hclose` forces every element of `H` to be within `D` of
`1`, so `H` is bounded, and a bounded subgroup is quasiconvex at its own
diameter — consistent, and not vacuous.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Moving an endpoint moves the geodesic boundedly -/

/-- **Moving one endpoint by `D` moves the geodesic by at most `2D + 2δ`.**

Take `q` between `x` and `b'` at parameter `min (d(x,p)) (d(x,b'))`;
`Hyperbolic.exists_isBetween` supplies one at every prescribed parameter.  The
four-point condition at `(x, b', p, q)` then has both competing pairings at most
`d(x,b') + 2D`, so `d(p,q) ≤ 2D + 2δ`.

The minimum is what makes the two cases uniform: below it the first pairing is
exactly `d(x,b')`, above it the second collapses onto the triangle inequality
through `b`. -/
theorem exists_isBetween_near_of_endpoint_close {G : Type u} [Group G]
    {S : Set G} {delta D : ℕ} (hS : IsSymmetricGeneratingSet S)
    (hdelta : Hyperbolic.IsFourPointHyperbolic S delta) {x b b' p : G}
    (hp : Hyperbolic.IsBetween S x p b) (hbb : wordDist S b b' ≤ D) :
    ∃ q : G, Hyperbolic.IsBetween S x q b' ∧
      wordDist S p q ≤ 2 * D + 2 * delta := by
  have hle : min (wordDist S x p) (wordDist S x b') ≤ wordDist S x b' :=
    min_le_right _ _
  obtain ⟨q, hq, hqd⟩ := Hyperbolic.exists_isBetween hS x b' hle
  refine ⟨q, hq, ?_⟩
  have h4 := hdelta x b' p q
  have hb1 : wordDist S x p + wordDist S p b = wordDist S x b := hp
  have hb2 : wordDist S x q + wordDist S q b' = wordDist S x b' := hq
  have hc1 := wordDist_comm hS b' q
  have hc3 := wordDist_comm hS b' b
  have hc4 := wordDist_comm hS b p
  have htri1 := wordDist_triangle hS b' b p
  have htri2 := wordDist_triangle hS x b' b
  omega

/-! ## A between-point is near a prefix of a geodesic word -/

/-- **Every point between `1` and `b` is `2δ` from a prefix of any geodesic word
for `b`.**

The prefix at index `d(1,q)` is a between-point at the same parameter, by
`Hyperbolic.isBetween_of_geodesic_append`, and two between-points at the same
parameter are `2δ` apart.  This is what converts the abstract between-points the
four-point condition produces into the objects `IsWordQuasiconvex` speaks
about. -/
theorem exists_prefix_near_of_isBetween {G : Type u} [Group G] {S : Set G}
    {delta : ℕ} (hS : IsSymmetricGeneratingSet S)
    (hdelta : Hyperbolic.IsFourPointHyperbolic S delta) {b q : G}
    (hq : Hyperbolic.IsBetween S 1 q b) {w : List G} (hw : IsGeodesicWord S w b) :
    ∃ j ≤ w.length, wordDist S q ((w.take j).prod) ≤ 2 * delta := by
  have hwb : w.prod = b := hw.isWord.prod_eq
  have hlen : w.length = wordDist S 1 b := by
    rw [wordDist_one_left]
    exact hw.length_eq
  have hqb : wordDist S 1 q + wordDist S q b = wordDist S 1 b := hq
  refine ⟨wordDist S 1 q, by omega, ?_⟩
  set j := wordDist S 1 q with hj
  have hjw : j ≤ w.length := by omega
  have hsplit : w.take j ++ w.drop j = w := List.take_append_drop j w
  have hgw : IsGeodesicWord S w w.prod := by
    refine ⟨⟨hw.isWord.letters, rfl⟩, ?_⟩
    rw [hwb]
    exact hw.length_eq
  have hgw' : IsGeodesicWord S (w.take j ++ w.drop j)
      (w.take j ++ w.drop j).prod := by
    rw [hsplit]
    exact hgw
  obtain ⟨hbet, hpar⟩ := Hyperbolic.isBetween_of_geodesic_append hS (1 : G) hgw'
  rw [hsplit, one_mul, one_mul, hwb] at hbet
  rw [one_mul, List.length_take] at hpar
  have hpar' : wordDist S 1 ((w.take j).prod) = j := by
    rw [hpar]
    omega
  exact GGT.wordDist_le_two_mul_of_isBetween hS hdelta hq hbet (by omega)

/-! ## The transport -/

/-- **Quasiconvexity transports to a larger subgroup at bounded Hausdorff
distance.**

`H'` is quasiconvex at `σ`, sits inside `H`, and every element of `H` is within
`D` of `H'`; then `H` is quasiconvex at `σ + 2D + 4δ`.

The bound `hclose` is Dahmani--Guirardel--Osin's `d_Hau(E(h)(s), ⟨h⟩(s)) < ∞`,
which they get from `⟨h⟩` being of finite index in `E(h)` (their Lemma 6.5).  It
is a hypothesis here and not a leaf of this module. -/
theorem isWordQuasiconvex_of_close {G : Type u} [Group G] (A : Alphabet G)
    {delta D sigma : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic A.carrier delta)
    {H H' : Subgroup G} (hle : H' ≤ H)
    (hclose : ∀ b ∈ H, ∃ b' ∈ H', wordDist A.carrier b b' ≤ D)
    (hqc : IsWordQuasiconvex A H' sigma) :
    IsWordQuasiconvex A H (sigma + 2 * D + 4 * delta) := by
  have hS := A.symmetricGenerating
  intro b hb w hlet hprod hlen i hi
  have hgw : IsGeodesicWord A.carrier w w.prod := by
    refine ⟨⟨hlet, rfl⟩, ?_⟩
    rw [hprod, hlen, wordDist_one_left]
  have hsplit : w.take i ++ w.drop i = w := List.take_append_drop i w
  have hgw' : IsGeodesicWord A.carrier (w.take i ++ w.drop i)
      (w.take i ++ w.drop i).prod := by
    rw [hsplit]
    exact hgw
  obtain ⟨hbet, _hpar⟩ :=
    Hyperbolic.isBetween_of_geodesic_append hS (1 : G) hgw'
  rw [hsplit, one_mul, one_mul, hprod] at hbet
  obtain ⟨b', hb', hbb⟩ := hclose b hb
  obtain ⟨q, hq, hpq⟩ :=
    exists_isBetween_near_of_endpoint_close (D := D) hS hdelta hbet hbb
  obtain ⟨w', hw'⟩ := exists_isGeodesicWord hS b'
  obtain ⟨j, hjw, hqj⟩ := exists_prefix_near_of_isBetween hS hdelta hq hw'
  have hlen' : w'.length = wordDist A.carrier 1 b' := by
    rw [wordDist_one_left]
    exact hw'.length_eq
  obtain ⟨e, he, hle'⟩ :=
    hqc b' hb' w' hw'.isWord.letters hw'.isWord.prod_eq hlen' j hjw
  refine ⟨e, hle he, ?_⟩
  have t1 := wordDist_triangle hS ((w.take i).prod) q e
  have t2 := wordDist_triangle hS q ((w'.take j).prod) e
  omega

end HullSC
end GroupApproximation
