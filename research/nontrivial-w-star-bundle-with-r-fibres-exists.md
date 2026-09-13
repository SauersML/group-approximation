---
rg: 2
id: nontrivial-w-star-bundle-with-r-fibres-exists
kind: claim
title: A nontrivial strictly separable W*-bundle with all fibres the hyperfinite II_1 factor exists
root: true
distinct_from:
  gamma-failure-invisible-to-projection-comparison: that asks for a C*-algebra without uniform Gamma whose tracial ultrapower compares projections; this asks only for an abstract bundle, with no C*-algebra realizing it and no comparison hypothesis.
  toms-ah-counterexample-to-uniform-gamma: that is an algebra without uniform Gamma whose trace simplex is the Poulsen simplex (`toms-doubling-ah-trace-simplex-is-poulsen`); this is the bundle-theoretic existence question, which needs a Bauer simplex.
  bauer-gamma-failure-localizes-to-infinite-dim-point: that constrains where a nontrivial bundle fails local triviality; this asks whether any nontrivial one exists.
artifacts:
  - research/artifacts/tw-bundle-hunter-bundle-localization-2026-09-12.md
---

**OPEN.** There is a strictly separable continuous W*-bundle over a compact
metrizable space all of whose fibres are isomorphic to `R`, and which is not
isomorphic to `C_σ(K,R)`.

*Marked `root` because it is Question 3.14 of Bosa--Brown--Sato--Tikuisis--White--Winter
(arXiv:1506.03974).*  Mommaerts (arXiv:2606.12134, Remark 4.7) records that its
existence is not known.

**Why it matters for Toms--Winter.**  If no such bundle exists, every unital
simple separable nuclear non-elementary algebra with a Bauer trace simplex has
uniform Gamma (`bauer-uniform-gamma-iff-trivial-tracial-bundle`), so Toms--Winter
holds on all Bauer simplices (`uniform-gamma-algebras-satisfy-toms-winter`).
Every unital counterexample with a Bauer simplex yields such a bundle.

## Attempts

- **Twisted gluing along automorphisms: dead.**  Gluing trivial pieces along
  `Aut(R)`-valued transition data gives a locally trivial bundle, hence a trivial
  one (`r-fibre-w-star-bundle-locally-trivial-is-trivial`, by Popa--Takesaki
  contractibility).  No characteristic class of the base built from `Aut(R)`
  obstructs triviality.
- **Finite-dimensional bases and finite-dimensional neighbourhoods: dead.**
  - Ozawa's Corollary 16 (`r-fibre-w-star-bundle-finite-dim-base-is-trivial`)
    covers finite-dimensional bases.
  - By `bauer-gamma-failure-localizes-to-infinite-dim-point`, a witness fails
    local triviality only at points where every neighbourhood is
    infinite-dimensional.
  - Mommaerts's `M_2`-diagonal attachment over `N ∪ {∞}` with `R` fibres is
    trivial (his Remark 4.7).
- **Uniform spectral gap: not available.**  Mommaerts's obstruction to local
  triviality needs full fibres, and `R` has property Gamma.  His Remark 4.8
  knows no other obstruction.
- **Countable-dimensional bases: dead, including the former smallest shape.**
  This shape was the one-point compactification of the disjoint union of the
  cubes `[0,1]^n`, with central halving rates degenerating over the `n`-th cube.
  - `r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial` shows every R-fibre bundle over a countable union of closed finite-dimensional compacta is trivial.
  - It also gives `Z(M) ⊆ K^(∞)`, the stable kernel of the derived sequence of points with no finite-dimensional neighbourhood.
  - Why the rates cannot degenerate: exact central matrix units lifted from the added point are uniformly good on a neighbourhood. They are patched to the finite-dimensional remainder by one flip unitary, at a cost independent of dimension.
  - A witness base must contain a nonempty closed set all of whose nonempty relatively open subsets are infinite-dimensional, e.g. a Hilbert cube. Every two-piece patching scheme must fail there.
- **Algebras without uniform Gamma.**  Toms's AH algebra
  (`toms-ah-counterexample-to-uniform-gamma`) would give a witness if its trace
  simplex were Bauer.  It is not.  Its trace simplex, and that of the non-simple
  limit, is the Poulsen simplex (`toms-doubling-ah-trace-simplex-is-poulsen`).
  - A non-Bauer simplex is not the obstacle (2026-09-12, lane
    `ex-tw-projection-starved-bundle`). Every closed set of extreme traces spans
    a Bauer face whose completion is an R-fibre bundle
    (`closed-extreme-trace-sets-give-r-fibre-w-star-bundles`).
  - The obstacle is central halving: the block projections of Toms's towers make
    every such face bundle trivial
    (`toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces`).
- **A dimension-free certificate, and why Toms's mechanism is not yet one.**
  - **The certificate.** `trivial-r-fibre-bundles-compare-equal-trace-projections`:
    in `C_σ(K,R)` over any compact base, equal-trace projections are
    approximately equivalent in `‖·‖_{2,u}`.  So a bundle is a witness as soon as
    it contains equal-trace projections that are not approximately equivalent,
    with no dimension hypothesis on the base.
  - **Toms's non-simple system** (arXiv:2606.12188v2, Section 4) has exactly this
    obstruction in its uniform tracial completion.  But its connecting maps double
    the base, `X_{i+1} = X_i × X_i × CP^{j_i}`, through the two coordinate
    projections.  Point traces restrict to averages `½(τ_{x'} + τ_{x''})`.  The
    extreme traces are dense and do not form a closed set
    (`toms-doubling-ah-trace-simplex-is-poulsen`).  The diagonal branch traces
    Toms uses to evaluate the obstruction are extreme, and branch traces started
    at deep stages restrict to arbitrary empirical measures on the leaves.
  - **The single-projection variant** `X_{i+1} = X_i × CP^{j_i}` is a
    `C(X̂)`-algebra with Bauer simplex `Prob(X̂)`.  Its doubled virtual bundle only
    squares a top-degree Thom–Porteous class, which vanishes (heuristic; Toms's
    Lemma 1 Step 2 was not checked in full).  So that variant loses the
    obstruction.
  - **What a Toms-style witness needs:** doubling (independent copies of the old
    obstruction) together with a closed set of extreme traces.  These pull in
    opposite directions in the obvious presentation.  Details are in
    `research/artifacts/tw-hilbert-cube-projection-invariant-2026-09-12.md`.
  - **Doubling with diagonal points and free labels is always Poulsen.**
    - Setting: a diagonal system whose top part averages pullbacks along maps
      with a common right inverse (diagonal points) and a surjective joint map
      (free leaf labels), with summable contamination.
    - Result: its extreme boundary is dense
      (`toms-doubling-ah-trace-simplex-is-poulsen`).
    - This covers coordinate-projection doubling on full products, such as a
      Hilbert-cube inverse limit, whatever fixed-point structure is added.
    - Contamination that is not summable sends the normalized rank of the
      propagated pair to zero, so the pair vanishes in the completion.
    - What is left is correlated copies: a joint map that is not surjective.
      This competes with the independence of the two copies that Toms's
      Section 5 uses.  Not attempted.  Details are in
      `research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md`.
  - **Strict comparison cannot be kept.**
    `strict-comparison-bundle-certificate-vanishes`: in every exact algebra with
    strict comparison, equal-trace projections of the completion are
    approximately equivalent.  So a C*-algebraic witness certified this way fails
    strict comparison.  The bundle question itself has no comparison hypothesis.
- **What a strict-comparison witness must lack instead (2026-09-12, lane
  `ex-toms-winter`).** Let the bundle be the strict closure of a unital simple
  separable nuclear algebra that has strict comparison and tracially locally
  finite nuclear dimension but is not Z-stable.
  - By `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`, for large `N`
    its reduced powers contain no projection `P` with `E(P) = 1/N`. There is no
    uniform tracial halving of the unit, central or not.
  - Every fibre `R` halves its unit, but not uniformly over the base.
  - So such a witness is certified by an existence gap at a constant profile,
    not by a comparison gap.
- **Faces of arbitrary algebras, and block-balanced towers: dead (2026-09-12, lane
  `ex-tw-projection-starved-bundle`).**
  - **Admissible sources are wider than Bauer algebras.** Take any unital separable
    nuclear algebra with no finite-dimensional representation, simple or not, with any
    trace simplex. Over every closed set `K` of extreme traces its tracial completion is
    an R-fibre bundle over `K` (`closed-extreme-trace-sets-give-r-fibre-w-star-bundles`).
    A divisibility gap of the unit relative to `K`, at one `N`, is a witness.
  - **Central halving kills every face.** Suppose the algebra has asymptotically central
    approximate projections with trace `1/2` uniformly on all traces, with no balancing
    against other elements. Then every face bundle is trivial
    (`central-halving-trivializes-every-closed-bauer-face-bundle`, via Ozawa Theorem 15).
    Uniform property Γ implies central halving.
  - **Towers with central halving.** Towers whose connecting maps split into equal-rank
    orthogonal blocks have it (`block-balanced-towers-have-central-halving`). These
    include:
    - Toms's no-Γ algebra and his non-simple tower, whose diagonal branch traces with
      free labels give a Hilbert-cube face that is still trivial;
    - DHTW, HRW products, diagonal AH algebras, and all their corners.
  - **Compact rigidity does not transfer.** The Hopf doubling tower contains no copy of
    `M_2`, yet divides its unit over every face
    (`hopf-doubling-tower-has-no-m2-but-divides-unit-tracially`). So coordinate Euler
    mass and DHTW-type unit rigidity are not certificates.
  - **Remaining AH shape.** Connecting maps with no balanced block splitting from
    infinitely many stages, of higher stable rank, since simple stable-rank-one AH
    algebras have uniform Γ by Vaccaro's theorem (`ah-face-bundles-are-trivial`).
