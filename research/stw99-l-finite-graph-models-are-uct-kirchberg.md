---
rg: 2
id: stw99-l-finite-graph-models-are-uct-kirchberg
kind: claim
title: The two edge-padded loop graphs give UCT Kirchberg algebras with computed scaled K-theory
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

For a positive integer vector `u = (u_1,...,u_n)` let `E(u)` be the
finite graph with vertices `1..n`, one distinguished loop `d_i` at each
vertex `i`, and edges `a_{ij}^{(k)} : i -> j` for `1 <= k <= u_j`.  Its
adjacency matrix is `M(u)_{ij} = delta_{ij} + u_j`, so

```text
I - M(u)^t = -u 1^t,     K_0 = Z^n / Z u,     K_1 = { x : sum_i x_i = 0 } = Z^{n-1},
```

with coordinate vectors representing the vertex projections and the
all-ones vector representing the unit.  `C*(E(u))` is a unital
separable nuclear simple purely infinite algebra in the UCT class.

For the two models used in this program:

```text
u = (1,1,2):  C = C*(E(1,1,2)),  K_0(C) = Z e_C (+) Z b,  b = [p_1],  K_1(C) = Z^2,
              [p_2] = 2 e_C - b,   [p_3] = -e_C
u = (1,2):    B = C*(E(1,2)),    K_0(B) = Z e_B,  [p] = 2 e_B,  [q] = -e_B,  K_1(B) = Z
```

`{e_C, b}` is a genuine basis because the columns `(1,1,2)`, `(1,1,1)`,
`(1,0,0)` have determinant `-1`.
