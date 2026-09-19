import GroupApproximation.GGT.HyperbolicAdditiveTransfer

/-!
# Carrying a word chain into the geodesic model, and a bound back out

`Cayley D.alphabet` is not a geodesic space, so no hyperbolic argument can be
run on it directly: every such argument has to pass through a geodesic model,
which `CayleyGeodesicModel.modelQuot` supplies.  This module is the part of that
passage that does not depend on which hyperbolic argument is being run.

## What is here

`quasiGeodesicChain_map` — the vertex chain of a `(l,B)`-quasi-geodesic word
maps under a map of additive distortion `C` to a chain that is again
quasi-geodesic, with the SAME lower rate `l`, edges lengthened by at most `C`,
and the additive constant worsened by exactly `C`.  Both directions of
`HasAdditiveDistortion` are used, one for each clause.

`dist_le_of_dist_map_le` and `dist_map_le_of_dist_le` — a distance bound
transfers either way at an additive cost of `C`.  The first is what brings a
bound proved in the model back to `Cayley D.alphabet`.

## Why it is stated for `HasAdditiveDistortion` and not for the model

Nothing here is about Cayley graphs, polygons, or components: it is arithmetic
on `|dist (f a) (f b) - dist a b| ≤ C`.  Stated this way it applies to
`M.iota` through `M.hasAdditiveDistortion` for any `GeodesicModel M`, and it
cannot be invalidated by a change in the geometric argument downstream --- which
is the reason it is written before that argument is settled.

The chain hypotheses are in the shape `ElementaryMorseChord`'s
`exists_bound_chord_near_chain` and `exists_bound_chain_near_chord` consume, so
the output of `quasiGeodesicChain_map` feeds them without an adapter.
-/

namespace GroupApproximation
namespace GGT

universe u v

variable {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-! ## 1.  Distances transfer both ways -/

/-- **A bound in the target pulls back**, at an additive cost of `C`.  This is
what carries a bound proved in the geodesic model back to the Cayley graph. -/
theorem dist_le_of_dist_map_le {C K : ℝ} {f : X → Y}
    (hf : HasAdditiveDistortion C f) {a b : X} (h : dist (f a) (f b) ≤ K) :
    dist a b ≤ K + C := by
  have hd := hf a b
  rw [abs_le] at hd
  linarith [hd.1]

/-- **A bound in the source pushes forward**, at the same cost. -/
theorem dist_map_le_of_dist_le {C K : ℝ} {f : X → Y}
    (hf : HasAdditiveDistortion C f) {a b : X} (h : dist a b ≤ K) :
    dist (f a) (f b) ≤ K + C := by
  have hd := hf a b
  rw [abs_le] at hd
  linarith [hd.2]

/-! ## 2.  A quasi-geodesic chain stays quasi-geodesic -/

/-- **The image of a quasi-geodesic chain is quasi-geodesic.**  The lower rate
`l` is unchanged, the edge bound grows by `C`, and the additive constant grows
by `C`.

The two clauses use opposite halves of the distortion bound: the edge clause
needs `dist (f a) (f b) ≤ dist a b + C`, and the progress clause needs
`dist a b - C ≤ dist (f a) (f b)`. -/
theorem quasiGeodesicChain_map {C D l B : ℝ} {f : X → Y}
    (hf : HasAdditiveDistortion C f) (y : ℕ → X) (N : ℕ)
    (hedge : ∀ i, i < N → dist (y i) (y (i + 1)) ≤ D)
    (hprog : ∀ i j, i ≤ j → j ≤ N →
      l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j)) :
    (∀ i, i < N → dist (f (y i)) (f (y (i + 1))) ≤ D + C) ∧
      (∀ i j, i ≤ j → j ≤ N →
        l * ((j - i : ℕ) : ℝ) - (B + C) ≤ dist (f (y i)) (f (y j))) := by
  constructor
  · intro i hi
    have hd := hf (y i) (y (i + 1))
    have he := hedge i hi
    rw [abs_le] at hd
    linarith [hd.2]
  · intro i j hij hjN
    have hd := hf (y i) (y j)
    have hp := hprog i j hij hjN
    rw [abs_le] at hd
    linarith [hd.1]

end GGT
end GroupApproximation
