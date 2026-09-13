---
rg: 2
id: fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3-proof
kind: route
title: "Mayer--Vietoris for the Bass--Serre tree gives infinite rational H_3 over an edge with infinite rational H_2"
target: fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3
requires: []
---

`K` acts without inversions on its Bass–Serre tree `T`. There are finitely
many orbits of vertices and edges, with stabilizers conjugate to the `G_v` and
the `G_e`. Since `T` is contractible, its augmented cellular chain complex
with rational coefficients is a short exact sequence of `QK`-modules

    0 → ⊕_e Q[K/G_e] → ⊕_v Q[K/G_v] → Q → 0,

with one summand per orbit (Serre, *Trees*, I.4). Apply `H_*(K; −)` and use
Shapiro's lemma, `H_k(K; Q[K/S]) ≅ H_k(S; Q)`. The long exact sequence
contains

    H_3(K; Q) → ⊕_e H_2(G_e; Q) --∂--> ⊕_v H_2(G_v; Q).

This is the Mayer–Vietoris sequence of a graph of groups (Chiswell, J. Pure
Appl. Algebra 8 (1976); Bieri, *Homological dimension of discrete groups*,
Theorems 2.10 and 2.12, for one edge).

- By hypothesis the source of `∂` is infinite-dimensional and the target is
  finite-dimensional, because both sums are finite. So `ker ∂` is
  infinite-dimensional.
- By exactness `H_3(K; Q)` maps onto `ker ∂`, so it is infinite-dimensional.

If `K` were of type `FP_3(Q)`, there would be a projective resolution
`P_* → Q` over `QK` with `P_0, …, P_3` finitely generated. Then `H_3(K; Q)`
would be a subquotient of the finite-dimensional space `P_3 ⊗_{QK} Q`, which
is impossible.

Type `FP_3` over `Z` implies `FP_3(Q)` (tensor a resolution with `Q`), and
`F_3` implies `FP_3`. So `K` is not of type `FP_3`, `F_3` or `F_∞`.
