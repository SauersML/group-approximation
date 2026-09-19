import GroupApproximation.GGT.DGOShortIsolatingCycleMain

/-!
# The isolated-component bound for a 4-gon, at `mu = 1` and any `b`

`exists_short_isolating_cycle` manufactures, from a 4-gon carrying an isolated
`H lam`-component as its distinguished side, a closed admissible word of length
at most `100 (delta + b + 1)` in which the component is still isolated and has
the same span.  `relBall_of_isolated_of_closed` --- Dahmani--Guirardel--Osin's
Lemma 4.6, the only device in their §4.2 that turns geometry into a bound on
`d_lam` --- converts that into

    d_lam(a_-, a_+) <= 100 (delta + b + 1) .

This module is that composition, and nothing else.  Both halves are proved:
there is no hypothesis here beyond hyperbolicity of the alphabet, symmetry of
the base (which `OsinTheorem54SepSymmetric.exists_symmetric_base` supplies for
free) and the polygon itself.

## The constant, and why it is `delta + b + 1`

Thinness of a `(1,b)`-quasi-geodesic quadrangle costs `12 delta + 2 b`: the
source vertex is only `b`-almost between its side's corners and must be replaced
by a genuine between-point (`b + 2 delta`), the quadrangle itself costs `8 delta`
in the worst alternative, and the half-step back to an indexed vertex costs
`2 delta + b`.  The corner offset is correspondingly `theta + 3 + b`, since an
offset measured along a `(1,b)`-side yields `b` less than its index distance.
The worst branch of the case tree is then `96 delta + 21 b + 14`, and
`100 (delta + b + 1)` covers it with room to spare while keeping the shape the
`(1,0)` statement had --- only `delta` has become `delta + b`.

At `b = 0` the thinness constant is `12 delta` rather than the `10 delta` a
purely geodesic argument gives, because the replacement step costs `2 delta`
even when the source is already between.  One case tree was preferred to two;
nothing downstream is sharp in `delta` anyway, Osin's Lemma 4.2 quantifying its
constant existentially.

## The two shapes

`isolatedComponentBound_geodesicFourGon` takes the polygon as a
`GeodesicFourGon` with its cut function named.  That is the shape the
construction is stated in.

`span_mem_relBall_of_sideZero` takes it as the unpacked clauses of
`IsQuasiGeodesicPolygon D 1 b 4 v w` with the cut function named and **side `0`
exempt** from the quasi-geodesic clause.  That is the *side form* of the bound at
`n = 4`, `t = 0`, which is what
`DGOIsolatedComponentSideForm.sideForm_of_baseCase` consumes.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Lemma 4.16 composed with Lemma 4.6 -/

/-- **Dahmani--Guirardel--Osin's §4.2 bound for a 4-gon at `mu = 1`.**

For a 4-gon in `Gamma(G, X u H)` whose sides other than the distinguished one
are `(1,b)`-quasi-geodesic, and whose distinguished side is an isolated
`H lam`-component,

    d_lam(a_-, a_+) <= 100 (delta + b + 1) .

The cycle is built by `exists_short_isolating_cycle` and converted by
`relBall_of_isolated_of_closed`.  The span of the component at index `0` of the
cycle is *literally the same group element* as the span of the distinguished
side, so no estimate is lost in the conversion --- that is the point of carrying
the span through every splice. -/
theorem isolatedComponentBound_geodesicFourGon (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (lam : Λ) {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {δ b : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (hQ : GeodesicFourGon D b v w c) (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) :
    (vertex v w (c 0))⁻¹ * vertex v w (c 1)
      ∈ D.relBall lam (100 * (δ + b + 1)) := by
  obtain ⟨u, q, hq1, hq2, hq3, hq4, hq5, hq6⟩ :=
    exists_short_isolating_cycle D hsymm lam hδ hQ hcomp hiso
  have hball : (vertex u q 0)⁻¹ * vertex u q 1 ∈ D.relBall lam q.length :=
    relBall_of_isolated_of_closed D hsymm lam u hq1 hq2 hq4 hq5
  rw [hq6] at hball
  exact relBall_mono_radius D lam hq3 hball

/-! ## The side form -/

/-- **A side with the `(1,b)` progress clause is a `(1,b)`-quasi-geodesic
chain.**

The lower bound `(q - p)/1 - b <= d` is the quasi-geodesic clause at `mu = 1`;
the matching upper bound `d <= q - p` holds for any word, consecutive vertices
being one alphabet letter apart (`wordDist_vertex_le'`).  The real clause is
transported as the natural `x <= d + b`, which is the shape truncated
subtraction is recovered from. -/
theorem isGeodesicChain_of_progress (D : RelGenSet G Λ) {v : G}
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i₀ k₀ b : ℕ}
    (hik : i₀ ≤ k₀) (hk : k₀ ≤ w.length)
    (hqg : ∀ p q : ℕ, i₀ ≤ p → p ≤ q → q ≤ k₀ →
      ((q - p : ℕ) : ℝ) / 1 - (b : ℝ)
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ)
            : ℝ)) :
    IsQuasiGeodesicChain D.alphabet.carrier b (fun m => vertex v w (i₀ + m))
      (k₀ - i₀) := by
  intro x y hxy hyn
  show (y - x) - b
      ≤ wordDist D.alphabet.carrier (vertex v w (i₀ + x))
        (vertex v w (i₀ + y)) ∧
    wordDist D.alphabet.carrier (vertex v w (i₀ + x))
      (vertex v w (i₀ + y)) ≤ y - x
  have hupper := wordDist_vertex_le' D hlet v
    (show i₀ + x ≤ i₀ + y by omega) (show i₀ + y ≤ w.length by omega)
  have hlow := hqg (i₀ + x) (i₀ + y) (by omega) (by omega) (by omega)
  rw [div_one] at hlow
  have hlow' : ((i₀ + y - (i₀ + x) : ℕ) : ℝ)
      ≤ ((wordDist D.alphabet.carrier (vertex v w (i₀ + x))
        (vertex v w (i₀ + y)) : ℕ) : ℝ) + (b : ℝ) := by linarith
  have hlower : i₀ + y - (i₀ + x)
      ≤ wordDist D.alphabet.carrier (vertex v w (i₀ + x))
          (vertex v w (i₀ + y)) + b := by exact_mod_cast hlow'
  omega

/-- **The side form of the §4.2 bound at `(1,b)`, `n = 4`, `t = 0`.**

The polygon is taken apart into its clauses, with the cut function named and
side `0` --- the one carrying the component --- **exempt** from the
quasi-geodesic clause, as in Dahmani--Guirardel--Osin's Definition 4.13.  A
maximal run whose vertices all lie in one coset of `H lam` is never a
quasi-geodesic chain at `b` smaller than its length, so demanding the clause of
the component side is what forced the recut to pay. -/
theorem span_mem_relBall_of_sideZero (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ b : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hc4 : c 4 = w.length)
    (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hcqg : ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
      q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / 1 - (b : ℝ)
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ)
            : ℝ))
    (lam : Λ) (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) :
    (vertex v w (c 0))⁻¹ * vertex v w (c 1)
      ∈ D.relBall lam (100 * (δ + b + 1)) := by
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have hQ : GeodesicFourGon D b v w c := by
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
with the arguments in its order and `C = 25 (delta + b + 1)`, so that `C * N` at
`N = 4` is the `100 (delta + b + 1)` proved above.  Against the `(1,0)` version
only one thing has moved: `delta + 1` has become `delta + b + 1`.

`c 1 = 1` is not actually needed --- `span_mem_relBall_of_sideZero` collapses a
run of any length through `normWord` --- and is taken only so that this
statement matches the binder verbatim.

**What is still open** is the range of `N`: the transfer needs the binder for
every `N <= 6`, and what is proved here is `N = 4`.  Dahmani--Guirardel--Osin's
Lemma 4.17 reaches the rest by a purely combinatorial diagonal cut from this
base case. -/
theorem baseCase_of_sideZero (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ b : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hc1 : c 1 = 1) (hc4 : c 4 = w.length)
    (hcmono : ∀ s : ℕ, c s ≤ c (s + 1)) (lam : Λ)
    (hcqg : ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
      q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / 1 - (b : ℝ)
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ)
            : ℝ))
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0) :
    (vertex v w 0)⁻¹ * vertex v w 1
      ∈ D.relBall lam (25 * (δ + b + 1) * 4) := by
  have hcompc : IsComp lam w (c 0) (c 1) := by
    rw [hc0, hc1]
    exact hcomp
  have hisoc : IsIsolated D.fam lam v w (c 0) := by
    rw [hc0]
    exact hiso
  have hmain := span_mem_relBall_of_sideZero D hsymm hδ v w c hlet hclosed hc0
    hc4 hcmono hcqg lam hcompc hisoc
  rw [hc0, hc1] at hmain
  have hrad : 25 * (δ + b + 1) * 4 = 100 * (δ + b + 1) := by ring
  rw [hrad]
  exact hmain

end OsinComponents
end GGT
end GroupApproximation
