---
rg: 2
id: non-proper-power-one-relator-complexes-are-aspherical
kind: claim
title: The presentation complex of a one-relator presentation whose cyclically reduced relator is not a proper power is aspherical
distinct_from:
  locally-indicable-2-complex-with-h2-zero-is-aspherical: that is Howie's criterion for arbitrary 2-complexes with locally indicable fundamental group and H_2 = 0; this is the one-relator case (Lyndon, Cockcroft), decided by the relator alone.
  cprime-one-sixth-presentations-hyperbolic-and-torsion-free: that gives asphericity for C'(1/6) presentations; this covers every one-relator presentation with a cyclically reduced relator that is not a proper power, with no small-cancellation hypothesis.
---

Imported through `non-proper-power-one-relator-complexes-aspherical-citation` (Asphericity
Theorem of the Linton–Nyberg-Brodda survey, attributed there to Cockcroft 1954 and Lyndon 1950).

**Claim.** Let `X` be a finite alphabet and let `w ∈ F(X)` be a nontrivial, cyclically reduced
word that is not a proper power in `F(X)`. Let `K` be the presentation complex of `<X | w>`. It has
one 0-cell, a 1-cell for each `x ∈ X`, and one 2-cell attached along the edge path spelling `w`.
Then `K` is aspherical.

**Consequences used downstream.**
- Every connected covering space of `K` is aspherical, because it has the same higher homotopy
  groups.
- If `H ≤ G = <X | w>` has finite index `k`, the corresponding cover `K_H` is a finite
  2-dimensional `K(H,1)`. It has `k` vertices, `k|X|` edges and `k` 2-cells, so
  `χ(K_H) = k(2 − |X|)`. For `|X| = 2` this is `0`.

The import is used by `virtual-fibring-collapse-certificate-proof`.
