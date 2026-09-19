import GroupApproximation.GGT.DGOPolygonBaseCaseTower

/-!
# The six-side bound at `μ = 1`, discharged

`DGOPolygonBaseCaseTower.isolatedComponentBound_of_fourPointHyperbolic_at`
proves Osin's Lemma 4.2 for `(1,b)`-quasi-geodesic polygons with `n ≤ 6` sides,
at a NATURAL number `b`, from `hsymm` and four-point hyperbolicity of the
relative graph alone.  The chain's consumers quote the bound with a REAL `b`,
because `IsQuasiGeodesicPolygon` does, so this module bridges the two: a
`(1,b)`-quasi-geodesic polygon is a `(1,⌈b⌉₊)`-quasi-geodesic one --- widening
the defect only weakens the clause --- and the constant comes back from the
tower at `⌈b⌉₊`.

## What this does and does not discharge

It discharges the `μ = 1` slice, which is the whole of what this development
uses: the relator chain's polygons are `(1, |p| + c)`-quasi-geodesic, and the
polygons of Osin's own §4 arguments are geodesic, `(1,0)`.  Nothing in the tree
feeds a `μ > 1` polygon.

It does NOT produce the `∀ mu b, 1 ≤ mu → 0 ≤ b → …` form that
`DGOIsolatedComponentCut.connector_mem_relBall` and the theorems above it quote,
and no argument can: a `(μ,b)`-quasi-geodesic with `μ > 1` is not a `(1,b')`-one
for any `b'`, the two clauses differing by an unbounded amount as `j - i` grows.
Consuming this requires those binders to be narrowed to `μ = 1`, which is one
line in each and changes no proof, since each applies the bound at the same
constants it received.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Widening the defect weakens the polygon clause.** -/
theorem isQuasiGeodesicPolygon_mono_defect (D : RelGenSet G Λ) {b b' : ℝ}
    (hbb : b ≤ b') {n : ℕ} {v : G} {u : List (RelLetter G Λ)}
    (hpoly : IsQuasiGeodesicPolygon D 1 b n v u) :
    IsQuasiGeodesicPolygon D 1 b' n v u := by
  obtain ⟨hlet, hclosed, c, hc0, hcn, hcmono, hcqg⟩ := hpoly
  refine ⟨hlet, hclosed, c, hc0, hcn, hcmono, ?_⟩
  intro s hs i j hi hij hj
  have h := hcqg s hs i j hi hij hj
  linarith

/-- **Osin's Lemma 4.2 at `μ = 1`, for every real defect, discharged.**

This is `DGOIsolatedComponentCut.connector_mem_relBall`'s `hbound` with `mu`
fixed at `1` --- the only value anything in this development instantiates --- and
it is a theorem, not a binder: its inputs are the symmetry of the base and
four-point hyperbolicity of `Γ(G, X ⊔ ℋ)`. -/
theorem sixBound_one_of_fourPointHyperbolic (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∀ b : ℝ, 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D 1 b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n) := by
  intro b _hb
  refine ⟨15 * (25 * (δ + ⌈b⌉₊ + 1)), by omega, ?_⟩
  intro n hn v u hpoly nu i k hcomp hiso
  exact isolatedComponentBound_of_fourPointHyperbolic_at D hsymm ⌈b⌉₊ hδ n hn v u
    (isQuasiGeodesicPolygon_mono_defect D (Nat.le_ceil b) hpoly) nu i k hcomp
    hiso

end OsinComponents
end GGT
end GroupApproximation
