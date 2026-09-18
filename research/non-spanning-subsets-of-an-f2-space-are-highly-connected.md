---
rg: 2
id: non-spanning-subsets-of-an-f2-space-are-highly-connected
kind: claim
title: The simplicial complex of non-spanning sets of nonzero vectors of F_2^r is (r-3)-connected
distinct_from:
  integral-affine-splitting-types-have-finitely-many-tuple-orbits: that is an orbit count for halving directions; this is the connectivity input replacing the boundary of a simplex in the descending-link analysis when the colors form a vector space.
---

**ESTABLISHED** (lane proof from standard results, recalled and not re-read: the Nerve
Lemma, Rota's crosscut theorem, and Solomon–Tits).

Let `U = F_2^r` with `r ≥ 1`, and let `K(U)` be the simplicial complex with vertex set
`U ∖ {0}` whose simplices are the finite sets `A` with `span(A) ≠ U`.

**Claim.** `K(U)` is `(r − 3)`-connected. For `r = 1` it is empty, which is
`(−2)`-connected; for `r = 2` it is three points.

**Proof.** `K(U)` is covered by the full simplices `Δ(H ∖ 0)`, one for each hyperplane
`H ≤ U`, since a set fails to span exactly when it lies in a hyperplane. A family of these
simplices intersects in `Δ((H_1 ∩ … ∩ H_j) ∖ 0)`, which is a nonempty simplex exactly when
`H_1 ∩ … ∩ H_j ≠ 0`. By the Nerve Lemma, `K(U)` is homotopy equivalent to the complex of
sets of hyperplanes with nonzero intersection. By the crosscut theorem, that complex is
homotopy equivalent to the order complex of the proper part of the subspace lattice of `U`,
the Tits building of `GL_r(F_2)`. By Solomon–Tits, the building is a wedge of
`(r − 2)`-spheres, hence `(r − 3)`-connected. ∎

**Use.** In Belk–Zaremsky's descending split link (arXiv:2001.04579, Lemma 7.6), the nerve is
the boundary of a simplex on pairs `(root, color)`. When colors are halving directions
spanning a vector space `U_i` per root, the corresponding nerve is the union
`⋃_i (Δ_1 ∗ … ∗ K(U_i) ∗ … ∗ Δ_q) ≃ Σ^{q−1}(K(U_1) ∗ … ∗ K(U_q))`. This is
`(Σ_i dim U_i − 3)`-connected, the same bound as theirs with `|Spec|` replaced by `dim U_i`.
See `twisted-integral-affine-group-fp-via-stein-complex`.
