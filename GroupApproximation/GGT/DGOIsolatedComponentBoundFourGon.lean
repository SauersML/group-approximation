import GroupApproximation.GGT.DGOShortIsolatingCycleMain

/-!
# The isolated-component bound for a 4-gon, at `mu = 1`, `b = 0`

`exists_short_isolating_cycle` manufactures, from a 4-gon carrying an isolated
`H lam`-component as its distinguished side, a closed admissible word of length
at most `100 (delta + 1)` in which the component is still isolated and has the
same span.  `relBall_of_isolated_of_closed` --- Dahmani--Guirardel--Osin's
Lemma 4.6, the only device in their §4.2 that turns geometry into a bound on
`d_lam` --- converts that into

    d_lam(a_-, a_+) <= 100 (delta + 1) .

This module is that composition, and nothing else.  Both halves are proved:
there is no hypothesis here beyond hyperbolicity of the alphabet, symmetry of
the base (which `OsinTheorem54SepSymmetric.exists_symmetric_base` supplies for
free) and the polygon itself.

## The two shapes

`isolatedComponentBound_geodesicFourGon` takes the polygon as a
`GeodesicFourGon` with its cut function named.  That is the shape the
construction is stated in.

`span_mem_relBall_of_sideZero` takes it as the unpacked clauses of
`IsQuasiGeodesicPolygon D 1 0 4 v w` with the cut function named and **side `0`
exempt** from the quasi-geodesic clause.  That is the *side form* of the bound at
`n = 4`, `t = 0`, which is what `DGOIsolatedComponentRecut.span_mem_relBall_of_sideForm`
consumes: the recut turns a component lying inside a side of an `n`-gon into a
component that *is* a side of an `(n+2)`-gon, and the exemption is what lets a
straddling run be recut without paying `b |-> b + 1`.

What is still missing between the two is the *rotation*: the side form quantifies
over every side `t < N` and over `N <= 6`, while what is proved here is `t = 0`,
`N = 4`.  Dahmani--Guirardel--Osin get the other sides from "changing the
enumeration of the sides", which for a named cut function is a re-indexing of
`c`; it is index bookkeeping over this theorem, not new geometry, and it is not
done here.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Lemma 4.16 composed with Lemma 4.6 -/

/-- **Dahmani--Guirardel--Osin's §4.2 bound for a 4-gon at `mu = 1`, `b = 0`.**

For a 4-gon in `Gamma(G, X u H)` whose sides other than the distinguished one are
geodesic, and whose distinguished side is an isolated `H lam`-component,

    d_lam(a_-, a_+) <= 100 (delta + 1) .

The cycle is built by `exists_short_isolating_cycle` and converted by
`relBall_of_isolated_of_closed`.  The span of the component at index `0` of the
cycle is *literally the same group element* as the span of the distinguished
side, so no estimate is lost in the conversion --- that is the point of carrying
the span through every splice. -/
theorem isolatedComponentBound_geodesicFourGon (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (lam : Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (hQ : GeodesicFourGon D v w c) (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) :
    (vertex v w (c 0))⁻¹ * vertex v w (c 1)
      ∈ D.relBall lam (100 * (δ + 1)) := by
  obtain ⟨u, q, hq1, hq2, hq3, hq4, hq5, hq6⟩ :=
    exists_short_isolating_cycle D hsymm lam hδ hQ hcomp hiso
  have hball : (vertex u q 0)⁻¹ * vertex u q 1 ∈ D.relBall lam q.length :=
    relBall_of_isolated_of_closed D hsymm lam u hq1 hq2 hq4 hq5
  rw [hq6] at hball
  exact relBall_mono_radius D lam hq3 hball

/-! ## The side form -/

/-- **A side with the `(1,0)` progress clause is a geodesic chain.**

The lower bound `(q - p)/1 - 0 <= d` is the quasi-geodesic clause at `mu = 1`,
`b = 0`; the matching upper bound `d <= q - p` holds for any word, consecutive
vertices being one alphabet letter apart (`wordDist_vertex_le'`).  This is
`exists_geodesicChain_of_isQuasiGeodesicPolygon` for one side, taken apart so
that a caller who has the clause for *some* sides only can use it on those. -/
theorem isGeodesicChain_of_progress (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i₀ k₀ : ℕ}
    (hik : i₀ ≤ k₀) (hk : k₀ ≤ w.length)
    (hqg : ∀ p q : ℕ, i₀ ≤ p → p ≤ q → q ≤ k₀ →
      ((q - p : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ)) :
    IsGeodesicChain D.alphabet.carrier (fun m => vertex v w (i₀ + m))
      (k₀ - i₀) := by
  intro a b hab hbn
  show wordDist D.alphabet.carrier (vertex v w (i₀ + a)) (vertex v w (i₀ + b))
      = b - a
  have hupper := wordDist_vertex_le' D hlet v
    (show i₀ + a ≤ i₀ + b by omega) (show i₀ + b ≤ w.length by omega)
  have hlow := hqg (i₀ + a) (i₀ + b) (by omega) (by omega) (by omega)
  rw [div_one, sub_zero] at hlow
  have hlower : i₀ + b - (i₀ + a)
      ≤ wordDist D.alphabet.carrier (vertex v w (i₀ + a))
          (vertex v w (i₀ + b)) := by exact_mod_cast hlow
  omega

/-- **The side form of the §4.2 bound at `(1,0)`, `n = 4`, `t = 0`.**

The polygon is taken apart into its clauses, with the cut function named and
side `0` --- the one carrying the component --- **exempt** from the
quasi-geodesic clause, as in Dahmani--Guirardel--Osin's Definition 4.13.  This
is the shape `DGOIsolatedComponentRecut.span_mem_relBall_of_sideForm` consumes,
and the exemption is what its straddling-run obstruction needs: a maximal run
whose vertices all lie in one coset of `H lam` is never a geodesic chain, so
demanding the clause of the component side is what forced `b |-> b + 1`.

`C = 100 (delta + 1)` here rather than `C * N`: with `N = 4` fixed the two are
interchangeable, and the constant of Osin's Lemma 4.2 is quantified
existentially by its consumers. -/
theorem span_mem_relBall_of_sideZero (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hc4 : c 4 = w.length)
    (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hcqg : ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
      q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (lam : Λ) (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) :
    (vertex v w (c 0))⁻¹ * vertex v w (c 1)
      ∈ D.relBall lam (100 * (δ + 1)) := by
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have hQ : GeodesicFourGon D v w c := by
    refine ⟨hlet, hclosed, hc0, hc4, hmono, ?_⟩
    intro t ht ht0
    have hcs : c t ≤ c (t + 1) := hcmono t
    have hub : c (t + 1) ≤ w.length := by
      rw [← hc4]
      exact hmono (show t + 1 ≤ 4 by omega)
    exact isGeodesicChain_of_progress D hlet hcs hub (hcqg t ht ht0)
  exact isolatedComponentBound_geodesicFourGon D hsymm lam hδ hQ hcomp hiso

/-- **The base case in the shape the side-form transfer consumes, at `N = 4`.**

The binder that `DGOIsolatedComponentSideForm.sideForm_of_baseCase` asks for,
with the arguments in its order and `C = 25 (delta + 1)`, so that `C * N` at
`N = 4` is the `100 (delta + 1)` proved above.  The five load-bearing features of
that binder are all present: `c 1 = 1` is an input (side `0` is exempt, so it
cannot be derived), the quasi-geodesic clause is asked only of the sides
`s <> 0`, the component and its isolation are at index `0`, and `C` does not
depend on the word.

`c 1 = 1` is not actually needed --- `span_mem_relBall_of_sideZero` collapses a
run of any length through `normWord` --- and is taken only so that this
statement matches the binder verbatim.

**What is still open** is the range of `N`: the transfer needs the binder for
every `N <= 6`, because the recut of a component lying strictly inside a side of
a 4-gon produces a 6-gon, and what is proved here is `N = 4`.  The obstruction is
not the thinness constant, which
`exists_isBetween_of_quadrangle` generalises to more corners by more diagonal
cuts; it is the case tree.  Two of its branches use that the sides *between* the
two flanks form a single geodesic: the short branch bounds their total length by
one distance, and the double branch bounds the kept middle segment by the
distance between the two near vertices.  With more than one side in between,
length is no longer distance and both bounds fail. -/
theorem baseCase_of_sideZero (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hc1 : c 1 = 1) (hc4 : c 4 = w.length)
    (hcmono : ∀ s : ℕ, c s ≤ c (s + 1)) (lam : Λ)
    (hcqg : ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
      q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0) :
    (vertex v w 0)⁻¹ * vertex v w 1 ∈ D.relBall lam (25 * (δ + 1) * 4) := by
  have hcompc : IsComp lam w (c 0) (c 1) := by
    rw [hc0, hc1]
    exact hcomp
  have hisoc : IsIsolated D.fam lam v w (c 0) := by
    rw [hc0]
    exact hiso
  have hmain := span_mem_relBall_of_sideZero D hsymm hδ v w c hlet hclosed hc0
    hc4 hcmono hcqg lam hcompc hisoc
  rw [hc0, hc1] at hmain
  have hrad : 25 * (δ + 1) * 4 = 100 * (δ + 1) := by ring
  rw [hrad]
  exact hmain

end OsinComponents
end GGT
end GroupApproximation
