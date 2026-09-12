---
rg: 2
id: nontrivial-w-star-bundle-with-r-fibres-exists
kind: claim
title: A nontrivial strictly separable W*-bundle with all fibres the hyperfinite II_1 factor exists
root: true
distinct_from:
  gamma-failure-invisible-to-projection-comparison: that asks for a C*-algebra without uniform Gamma whose tracial ultrapower compares projections; this asks only for an abstract bundle, with no C*-algebra realizing it and no comparison hypothesis.
  toms-ah-counterexample-to-uniform-gamma: that is an algebra without uniform Gamma whose trace simplex has not been checked to be Bauer; this is the bundle-theoretic existence question, which such an algebra would answer if its simplex were Bauer.
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
  simplex were Bauer.  Its paper does not address this, and it was not checked.
