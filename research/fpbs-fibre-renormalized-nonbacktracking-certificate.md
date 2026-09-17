---
rg: 2
id: fpbs-fibre-renormalized-nonbacktracking-certificate
kind: claim
title: Renormalizing a normal fibre into its susceptibility gives a backtrack-weighted Ihara certificate for nonuniqueness that cancels the fibre's own cycles
distinct_from:
  fpbs-nb-spectral-deficit-obstruction: that is the unrenormalized case chi = 1 (no fibre generators), whose product corollary needs the percolation deficit d-1-1/p_c of the whole graph and so is spoiled by short cycles of the amenable factor; this contracts the fibre clusters into their susceptibility, weights backtracks by (chi-1)/chi, and on products compares only the inter-fibre collision loss with the spectral margin of the nonamenable factor.
  fpbs-ew-nb-majorant: that bounds the connectivity operator of one regular graph by nonbacktracking walks; this bounds coset-summed connectivities through a quotient multigraph with fibre-susceptibility weights and a Woodbury reduction on directed quotient edges.
  fpbs-percolation-kesten-normal-gap: that asks for p_c(G) < p_c(N;G) on every generating set; this gives an explicit lower bound on p_c(N;G) in terms of chi_N and ||A_X||, and turns the product case into one collision-loss inequality.
  fpbs-tree-projected-critical-half-graph-transfer-below-one: that is a transfer condition at p_c on tree-projected sets with half-graph factors; this is an unconditional subcritical certificate for any normal subgroup split of the generating set.
artifacts:
  - experiments/fibre-renormalized-certificate-2026-09-17/saw_triangle_deficit.py
---

**ESTABLISHED.** Proof in `fpbs-fibre-renormalized-nonbacktracking-certificate-proof`.

**Setting.** `Gamma` finitely generated, `S` finite symmetric, `e ∉ S`,
`G = Cay(Gamma,S)`. `N` is an infinite normal subgroup, `Q = Gamma/N`,
`pi: Gamma -> Q`. Split `S = S_N ⊔ S'` with `S_N ⊂ N` symmetric (possibly
empty) and `S'` symmetric, `d' = |S'|`. Let `X` be the Schreier multigraph of
`Q` with one directed edge `(q, q pi(s))` for each `s ∈ S'` (a loop when
`s ∈ N`), and `A_X` its adjacency operator on `l2(Q)`. Put
`chi_N(p) = E_p|C_{S_N}(o)|`, the susceptibility of `Cay(<S_N>, S_N)`
(`chi_N = 1` if `S_N` is empty), and for `chi_N(p) < infinity`

```text
t = p chi_N(p),   gamma = 1/chi_N(p),
F_p(u) = 1 + gamma (d' - gamma) u^2 - u ||A_X||.
```

**Theorem A (certificate).** If `p < 1`, `chi_N(p) < infinity` and
`F_p(u) > 0` for all `u ∈ [0, t]`, then `E_p|C(o) ∩ qN| < infinity` for every
coset `qN`. Hence `p <= p_c(N;G)`, there is no unique infinite cluster at `p`,
and `p <= p_u(G)`. For `d' >= 1`, since `F_p` is convex with `F_p(0) = 1`, the
hypothesis holds iff `t ||A_X|| < 1 + gamma(d'-gamma) t^2` and `2 gamma (d'-gamma) t < ||A_X||`,
or the discriminant `||A_X||^2 - 4 gamma(d'-gamma)` is negative.

At `S_N = ∅` (`chi = gamma = 1`) the condition is `p < 1/sigma(||A_X||)`, i.e.
Theorems 1-2 of `fpbs-nb-spectral-deficit-obstruction` for infinite `N`.

**Theorem B (subcritical companion).** If `chi_N(p) < infinity` and
`p (d' chi_N(p) - 1) < 1`, then `E_p|C(o)| < infinity`, so `p <= p_c(G)`.

**Corollary C (products: the invariant a counterexample must carry).** Let
`G = Cay(H,S_H) □ Cay(B,S_B)` with `B` infinite, `N = B`, `S' = S_H`,
`d_H = |S_H|`, so `A_X = A_H` and `delta_H = d_H - ||A_H||`. For
`p ∈ (0, p_c(B))` write `chi = chi_B(p)`, `gamma = 1/chi`,
`kappa_p = 1/(p chi)` (the renormalized H-branching number) and the
**collision loss** `L_p = (d_H - gamma) - kappa_p`. Then:

1. for every `p ∈ (p_c(G), p_c(B))`: `L_p >= 0`;
2. if `p_c(G) = p_u(G)`, then for every `p ∈ (p_c(G), p_c(B))` at least one of
   * `L_p >= delta_H - gamma + p (d_H - gamma)`,
   * `p (d_H - gamma) > kappa_p` and `||A_H||^2 >= 4 gamma (d_H - gamma)`

   holds.

No quantity of `B` other than its susceptibility enters. The short cycles of
`B` (triangles of a spread-out factor), which make the whole-graph deficit
`D(G)` of order one, are absorbed into `chi_B`. So a product counterexample
must lose at least `delta_H` of its renormalized H-offspring to collisions
between fibre clusters. The open kill statement is
`fpbs-product-fibre-collision-loss-vanishes`.

**Why the renormalization is needed (computation).**
`experiments/fibre-renormalized-certificate-2026-09-17/saw_triangle_deficit.py`
bounds `p_c >= 1/lambda`, with `lambda` the exact Collatz–Wielandt bound for walks
that avoid backtracks and triangle closures on
`G_k = T_4 □ Cay(Z, {±1..±k})`. It gives

| `k` | `D(G_k) >=` |
|---|---|
| 16 | 0.5628 |
| 24 | 0.6189 |
| 32 | 0.6491 |
| 48 | 0.6811 |

All of these exceed `delta_H = 4 - 2 sqrt 3 = 0.5359` and also
`Delta(G_k) = d-1-sigma(d-delta_H)`, which is `0.5519, 0.5467, 0.5441, 0.5414`.
So for these graphs `D(G_k) >= Delta(G_k)`. The
unrenormalized certificate cannot certify them, and the example list of
`fpbs-product-amenable-factor-mean-field-deficit` ("spread-out balls") is not
mean-field at second order in the sense stated there. These particular graphs
have a tree factor and so strict thresholds by nonunimodularity; the point is
the certificate, not the thresholds.
