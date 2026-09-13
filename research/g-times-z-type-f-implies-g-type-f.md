---
rg: 2
id: g-times-z-type-f-implies-g-type-f
kind: claim
title: "Every group G such that G x Z is of type F is itself of type F"
distinct_from:
  g-times-z-type-f-iff-finitely-dominated-classifying-space: that is the established dictionary saying which groups have G x Z of type F and what separates them from type F groups; this is the open universal assertion that nothing separates them.
---

For every group `G`: if `G × Z` has a finite `K(π,1)`, then so does `G`.

This is the affirmative answer to M. C. B. Zaremsky, *Some open problems*
(version of July 12, 2026), Section 1, Problem 21: "For a group G, if G × Z
is of type F then is G of type F? This turns out to be equivalent to: If G
is of type F∞ and has finite cohomological dimension then is G of type F?"

By [[g-times-z-type-f-iff-finitely-dominated-classifying-space]] this claim
is equivalent to each of:

- every finitely presented group of type FP is of type F;
- every finitely dominated aspherical CW complex is homotopy equivalent to a
  finite CW complex;
- Wall's finiteness obstruction `σ(G) ∈ K̃_0(ZG)` vanishes for every group
  `G` with a finitely dominated `K(G,1)`.

Every group in question is torsion-free, since its cohomological dimension
is finite. The claim therefore follows from Hsiang's conjecture
`K̃_0(Z[π]) = 0` for torsion-free `π`, which the K-theoretic Farrell–Jones
conjecture implies.

## Attempts

- **Reduction to vanishing of `K̃_0`.** A counterexample `G` is a finitely
  presented torsion-free group of type FP whose Wall obstruction is a
  nonzero element of `K̃_0(ZG)`. So the claim holds for every `G` with
  `K̃_0(ZG) = 0`, in particular for `G` satisfying the K-theoretic
  Farrell–Jones conjecture. The general case contains the corresponding
  special case of Hsiang's conjecture: no torsion-free group with nonzero
  `K̃_0(Z[π])` is known (Ferry–Ranicki, arXiv:math/0008070, Section 2), and
  none is known to be the Wall obstruction of an aspherical space.
- **Splitting a finite `K(G × Z, 1)`.** By Mather's trick, `K(G,1) × S^1`
  is homotopy finite for every `G` with finitely dominated `K(G,1)`. So the
  hypothesis "G × Z is of type F" carries exactly the information "K(G,1) is
  finitely dominated", and a proof must show `σ(G) = 0`. Nothing about the
  circle factor can be used beyond that.
- **Contractible Rips complexes** (Problems 4.6 and 4.7, lanes
  z4-06-rips-finf-fcd and z4-07-type-f-rips). A torsion-free group acts
  freely and cocompactly on each of its Rips complexes. So a contractible
  Rips complex gives a finite `K(G,1)`, and a positive answer to 4.6 gives
  this claim. That route is open.
