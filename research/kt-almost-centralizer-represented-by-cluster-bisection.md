---
rg: 2
id: kt-almost-centralizer-represented-by-cluster-bisection
kind: claim
title: A permutation is represented by a total bisection of the cluster groupoid whose patch is Hamming-close to it
artifacts:
  - GroupApproximation/KunThom/CentralizerToBisectionOverlap.lean
  - GroupApproximation/KunThom/CentralizerToBisectionDefect.lean
  - GroupApproximation/KunThom/CentralizerToBisectionExtension.lean
  - GroupApproximation/KunThom/CentralizerToBisection.lean
  - GroupApproximation/KunThom/CentralizerToBisectionBound.lean
distinct_from:
  kt-patched-bisection-commutation-vanishes-with-threshold: that is the converse half of Kun--Thom Lemma 4.2(4), that patched bisections of cluster candidates almost commute with the labels; this is the forward half, that a given permutation is represented by a bisection whose patch is Hamming-close to it.
  kun-thom-sofic-centralizer-normalization: that is Kun--Thom Theorem 4.1 by citation; this is a finite lemma inside its proof, proved in Lean.
---

**ESTABLISHED, finite form.** Forward half of Kun--Thom, arXiv:2608.06222v3,
Lemma 4.2(4).

Let `D : PartialClusterSystem I L` be placed disjointly in a finite model `Y`
by `ι`, with an ambient labelled action `act`, and let `v` be a permutation of
`Y`.

* `overlapGood v` is the set of objects `X` such that the partial bijection
  `clusterOverlap v X Z` which `v` induces from `X` into some object `Z` is a
  cluster candidate. That `Z` is unique, and different good objects have
  different targets: a candidate misses fewer than `2 · scale` points on each
  side, and every object has at least `17 · scale` points.
* `representingPerm v` extends this object map to a permutation of `I` which
  keeps every object in its connectivity class. `representingBisection v` is a
  total bisection of `D.presentation.Obj`. At a good object its arrow is the
  class of the overlap arrow; elsewhere it is some candidate class.
* By the distance gap, a candidate within `16 · scale` of a representing arrow
  represents the same arrow, and the chosen representatives lie within
  `2 · scale` of the representing arrows.
* For every object map `π`, the patch `p` of the representing arrows satisfies

  `#{y : p y ≠ v y} ≤ #uncovered + 2 Σ_X sourceDefect(clusterOverlap v X (π X)) + 2 Σ_{X ∉ overlapGood v} |X|`.

* `#(overlapGood v)ᶜ · h · scale / 2` is at most the total forward plus inverse
  equivariance defect of `clusterOverlap v X (π X)`. The forward total is at most
  `|L|` times the total source defect plus
  `Σ_s (2 · #compatFailure s + #{y : v (act s y) ≠ act s (v y)})`. The inverse
  total is the same with target defects and `v⁻¹`, and `v⁻¹` has the
  commutation count of `v`.
* If every object has at most `K · scale` points, the mass outside
  `overlapGood v` is at most `2K / h` times that total defect.

Along a sofic approximation, suppose the uncovered mass, the compatibility
failures, the commutation defects of `v` and the leakage along the dominant
targets are all `o(|Y|)`, and the blocks have at most `K · scale` points. Then
the patch is within `o(|Y|) + (4K / h) · o(|Y|)` of `v`. The threshold `h` must
tend to zero (`kt-patched-bisection-commutation-vanishes-with-threshold`), so
the aggregate defects must be `o(h |Y|)`. Choosing that rate is part of the
scale parameter step.

## Frame defect: this does not compose with the chain

The statements above are proved for the global-scale `PartialClusterSystem`:
one threshold `h`, one `scale`, and `17 · scale ≤ |X|` for every object. The
Theorem 4.1 chain runs on `ScaledPartialClusterSystem`, with per-object scale
`|X| / 18` and pair scale `min (scale X) (scale Z)`. `CompressorNormalizationAssembly`'s
`hrep` has to return bisections of that presentation. Two consequences, found
by kt41-review (`research/artifacts/kt-theorem-4-1-review-2026-09-12.md`, R12):

* No producer gives `PartialClusterSystem.improveExists` for approximate
  component actions, so these bisections cannot be fed to the functor or to
  counting.
* At one global scale the count bound does not bound the mass outside
  `overlapGood v`: components can be far larger than `scale`.

The per-scale forward half, including the mass bound for bad objects, is owned
by lane kt41-bisection-rep on the landed `BlockEmbedding.bridge` API.
`BlockEmbedding.overlapArrow` duplicates `bridge`, and
`exists_perm_extending_fiberwise` does the job of
`CountingEndgame.exists_bisection_extend`. What carries over unchanged is the
finite arithmetic: uniqueness of candidate targets, the class-preserving
extension, the Hamming bound for arrows realizing `v`, and the candidate
criterion from forward and inverse defects.

## Plan correction

The patch of `BlockPatching.bisectionArrows b` takes each arrow through
`Quotient.out`. It can differ from `v` on up to `2 · scale` points per object,
and that total is not `o(|Y|)`. Hamming estimates against `v` must use
`representingArrows v`: its arrows are exactly the overlap arrows on good
objects, and they represent the same bisection.

Derivation: `kt-almost-centralizer-represented-by-cluster-bisection-proof`.
