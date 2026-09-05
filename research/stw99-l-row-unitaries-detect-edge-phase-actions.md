---
rg: 2
id: stw99-l-row-unitaries-detect-edge-phase-actions
kind: claim
title: Row unitaries over an edge-padded loop graph detect single-edge circle actions integrally
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

Keep the graphs `E(u)` of
`stw99-l-finite-graph-models-are-uct-kirchberg`, and order
`sum_j (u_j + 1)` columns by pairs `(j,k)`, `1 <= k <= u_j + 1`.  Define
the rectangular row `R_i` over `C*(E(u))` by

```text
(R_i)_{(j,k)} = s_{a_{ij}^{(k)}}   for k <= u_j
              = s_{d_i}            for k = u_j + 1, j = i
              = p_j                for k = u_j + 1, j != i
```

Then `R_i R_i^* = 1` and `R_i^* R_i = P` with `P` the SAME diagonal
projection for every `i` (it carries `u_j + 1` copies of `p_j`), so

```text
W_i = R_i R_n^*     is a unitary for every i < n.
```

Let `g_{ij,z}` be the automorphism multiplying the single edge
`a_{ij}^{(1)}` by `z` and fixing every other edge and every vertex; it is
one coordinate circle of the canonical `T^{E^1}` action, hence a
point-norm continuous circle action fixing all vertex projections.  For
`i < n`,

```text
g_{ij,z}(W_k) W_k^* = 1 + (z-1) s_{a_{ij}^{(1)}} s_{a_{ij}^{(1)}}^*   (k = i)
                    = 1                                              (k != i)
```

and therefore, in the invariant of
`stw99-l-pi1-aut-splits-into-two-hom-groups`,

```text
Delta_{g_{ij}}([W_k]) = delta_{ik} [p_j],     Delta_{g_{ij}} = 0 on K_0.
```

This is what makes the construction integral rather than rational: the
`K_1 -> K_0` value of an edge action is read off an EXPLICIT unitary,
with no appeal to an unnamed generator of graph `K_1`.
