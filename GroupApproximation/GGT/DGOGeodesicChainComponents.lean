import GroupApproximation.GGT.DGOPolygonGeodesicChain

/-!
# A geodesic chain never connects two of its own components

`OsinTheorem54SepFourGonGeneral.not_connected_of_isCompStart_of_geodesic` is this
statement for an `IsGeodesicWord D f g w` --- a whole word that is geodesic
between two named group elements.  A *side* of a polygon is not that: it is a
range of indices of a longer closed word, and what is known of it is
`IsGeodesicChain`, the form `GeodesicFourGon.geodesic` and the quasi-geodesic
clause at `(1,0)` deliver.  Concept grep before writing: no module on `main`
mentions `IsGeodesicChain` and `Connected` together, so the chain phrasing was
missing; the mathematics is not new and is quoted from the geodesic-word version.

## The argument, and where "geodesic" is stronger than "quasi-geodesic"

Two connected components have their initial vertices in one coset of `H lam`, so
they are one alphabet letter apart (`wordDist_le_one_of_mem_fam`); but distinct
component starts are at least two apart along the word
(`two_le_of_isCompStart`, since a component is a *maximal* run), and a geodesic
chain realises that separation as distance.  Two beats one.

This is the exact point at which geodesic is stronger than
`(μ,b)`-quasi-geodesic: for `μ(1 + b) ≥ 2` the two-apart estimate no longer
beats the one-letter bound, and the side `[comp lam h₁, base x, comp lam h₂]`
with `x ∈ X ∩ H_lam` is a `(3,0)`-quasi-geodesic whose two components *are*
connected.  So this lemma is available for the three geodesic sides of a
Dahmani--Guirardel--Osin 4-gon and not for the exempt one, which is as it should
be: the exempt side is a single component and has no second one to connect to.

## The one Lean detail worth naming

The chain is applied through an ascribed `have` at the beta-reduced type rather
than positionally.  Applying `hchain` to arguments leaves
`(fun m => vertex v w (c₀ + m)) (a - c₀)` as an un-reduced redex --- the lambda
is already in `hchain`'s type, so no metavariable is being instantiated and
nothing beta-reduces it --- and a following `rw` on the index would then find
nothing to rewrite.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **No two distinct components of a geodesic chain are connected.**

The chain is a range `[c₀, c₀ + n]` of indices of `w`, which is the shape a side
of a polygon comes in; the two component starts are required to lie in that
range and nothing else about them is assumed. -/
theorem not_connected_of_isCompStart_of_geodesicChain (D : RelGenSet G Λ)
    {lam : Λ} {v : G} {w : List (RelLetter G Λ)} {c₀ n : ℕ}
    (hchain : IsGeodesicChain D.alphabet.carrier
      (fun m => vertex v w (c₀ + m)) n)
    {i j : ℕ} (hi : IsCompStart lam w i) (hj : IsCompStart lam w j)
    (hne : i ≠ j) (hci : c₀ ≤ i) (hin : i ≤ c₀ + n) (hcj : c₀ ≤ j)
    (hjn : j ≤ c₀ + n) :
    ¬ Connected D.fam lam v w i j := by
  have key : ∀ a b : ℕ, a < b → c₀ ≤ a → b ≤ c₀ + n →
      IsCompStart lam w a → IsCompStart lam w b →
      Connected D.fam lam v w a b → False := by
    intro a b hab hca hbn ha hb hcon
    have hcon' : (vertex v w a)⁻¹ * vertex v w b ∈ D.fam lam := hcon
    have h2 : a + 2 ≤ b := two_le_of_isCompStart ha hb hab
    have h1 : wordDist D.alphabet.carrier (vertex v w a) (vertex v w b) ≤ 1 :=
      wordDist_le_one_of_mem_fam D hcon'
    have hd : wordDist D.alphabet.carrier (vertex v w (c₀ + (a - c₀)))
        (vertex v w (c₀ + (b - c₀))) = b - c₀ - (a - c₀) :=
      hchain (a - c₀) (b - c₀) (by omega) (by omega)
    rw [show c₀ + (a - c₀) = a from by omega,
      show c₀ + (b - c₀) = b from by omega,
      show b - c₀ - (a - c₀) = b - a from by omega] at hd
    omega
  intro hc
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key i j hlt hci hjn hi hj hc
  · exact key j i hgt hcj hin hj hi (connected_symm hc)

/-- **The same, for components given as `IsComp`.**  This is the form a caller
holding two runs of a side has; a run gives its start by
`IsCompStart lam w i = ⟨k, hcomp⟩`. -/
theorem not_connected_of_isComp_of_geodesicChain (D : RelGenSet G Λ) {lam : Λ}
    {v : G} {w : List (RelLetter G Λ)} {c₀ n : ℕ}
    (hchain : IsGeodesicChain D.alphabet.carrier
      (fun m => vertex v w (c₀ + m)) n)
    {i k j l : ℕ} (hi : IsComp lam w i k) (hj : IsComp lam w j l)
    (hne : i ≠ j) (hci : c₀ ≤ i) (hin : i ≤ c₀ + n) (hcj : c₀ ≤ j)
    (hjn : j ≤ c₀ + n) :
    ¬ Connected D.fam lam v w i j :=
  not_connected_of_isCompStart_of_geodesicChain D hchain ⟨k, hi⟩ ⟨l, hj⟩ hne hci
    hin hcj hjn

end OsinComponents
end GGT
end GroupApproximation
