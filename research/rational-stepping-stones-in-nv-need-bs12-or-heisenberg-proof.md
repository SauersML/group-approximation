---
rg: 2
id: rational-stepping-stones-in-nv-need-bs12-or-heisenberg-proof
kind: route
title: Explicit BS(1,2), BS(1,4), H_3(Z) and SL_3(Z) subgroups of the rational stepping stones
target: rational-stepping-stones-in-nv-need-bs12-or-heisenberg
requires: []
---

**Quotients of BS(1,k).** For `k >= 2`, `BS(1,k) = <s, u | u s u^-1 = s^k>
= Z[1/k] ⋊ Z`. Every proper quotient kills a power of `s`. The hand check in
`bs12-embeds-in-brin-thompson-2v` for `k = 2` works verbatim for every `k`: a
normal subgroup meeting `Z[1/k]` nontrivially contains `m Z[1/k]` for some
`m != 0`, and one meeting it trivially is centralized by `Z[1/k]`, so it is
trivial. Hence if `x, y` in a group satisfy `y x y^-1 = x^k` and `x` has
infinite order, then `<x, y> ≅ BS(1,k)`.

**Item 1.**
- `Aff(Q)` is the group of maps `z -> a z + b` with `a in Q^x`, `b in Q`. Put
  `x(z) = z + 1` and `y(z) = 2z`. Then `y x y^-1 (z) = 2(z/2 + 1) = z + 2`, so
  `y x y^-1 = x^2`, and `x` has infinite order. So `BS(1,2) <= Aff(Q)`.
- `Aff(Q) ≅ {[[a, b], [0, 1]]} <= B_2(Q) <= GL_2(Q) <= GL_n(Q)` for `n >= 2`,
  the last map being `g -> diag(g, I_(n-2))`.
- `SL_2(Q)` contains `x = [[1,1],[0,1]]` and `y = diag(2, 1/2)`, with
  `y x y^-1 = [[1,4],[0,1]] = x^4`. So `BS(1,4) <= SL_2(Q)`.
- `BS(1,4)` has index 2 in `BS(1,2)`: the subgroup `<s, u^2>` is
  `Z[1/2] ⋊ <u^2>`, where `u^2` acts by `4`, and `Z[1/2] = Z[1/4]`. So an
  embedding of `SL_2(Q)` in `nV` gives a virtual embedding of `BS(1,2)`.
- A group that virtually embeds in `nV` embeds in `nV` (Belk--Bleak--Matucci,
  arXiv:1602.08635, p. 2, as recorded in
  `zaremsky-2-19a-every-hyperbolic-group-in-some-nv-resolved`). Directly: if
  `H <= G` has index `k` and `H <= nV`, then `G <= H wr S_k` by
  Krasner--Kaloujnine. And `nV wr S_k <= nV`: split the Cantor cube into `k`
  subcubes by a complete prefix code of size `k` in the first coordinate,
  let `S_k` permute them by prefix replacement, and put a copy of `nV` on each
  subcube by conjugating with the prefix map.

**Item 2.** `U_3(Q)` contains `U_3(Z) = H_3(Z)`. For `n >= 3`,
`GL_n(Q) ⊇ SL_3(Z) ⊇ U_3(Z) = H_3(Z)`.

**Item 3.** For `n >= 3`, `GL_n(Q) ⊇ SL_3(Z)`, which is infinite with
property (T). ∎

**Model test.** The virtually abelian stepping stones avoid both gates:
`Q^x`, `Q^n`, the diagonal torus `(Q^x)^n` and `Q^n ⋊ (finite)` all embed in
`2V` (`countable-virtually-abelian-groups-embed-in-2v`), consistent with the
statement.
