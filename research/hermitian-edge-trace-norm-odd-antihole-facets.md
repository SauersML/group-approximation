---
rg: 2
id: hermitian-edge-trace-norm-odd-antihole-facets
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank facet of every odd antihole - admissible matrices on the complement of C_n have trace norm at least sqrt3 (n-2)
artifacts:
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/README.md
distinct_from:
  hermitian-edge-trace-norm-other-stab-facets: that is every full-support facet other than cliques and odd holes; this is the single family of odd antiholes with the all-ones weight.
  hermitian-edge-trace-norm-k4-free-h-perfect: that proves the odd-hole facets (C_n, n odd); this is their complements, which contain cliques of size (n-1)/2.
  hermitian-edge-trace-norm-clique-inequality: that is the clique facets; this facet is x(V) <= 2 on a graph with clique number (n-1)/2.
---

**OPEN - proved for every odd `n >= 7` except `n = 11`; `n = 11` is reduced to one bound on `K_5`
(`hermitian-edge-trace-norm-odd-antihole-c11`).** Let `n = 2k + 1 >= 7` and let `H = C̄_n` be the odd
antihole: vertices `Z_n`, with `i ~ j` iff `i - j` is not `0, +1, -1` mod `n`. Here `alpha(H) = 2`.
For every admissible `C` on `H` (Hermitian, zero diagonal, `C_ij = 0` on non-edges, `|C_ij| >= 1` on
edges),

```text
|| C ||_1  >=  sqrt3 ( n - 2 ) .
```

This is (**) at the weight `a = 1`, where `W - alpha_w = n - 2`.

**Why this facet.** An odd antihole is minimally imperfect, so `x(V) <= 2` is a facet of
`STAB(C̄_n)` (Padberg 1974). Antiwebs are rank-perfect (Wagler 2004), so every facet of
`STAB(C̄_n)` is a rank inequality `x(S) <= alpha(S)`. The only one with full support is therefore
`x(V) <= 2`. So this claim is exactly the odd-antihole part of
`hermitian-edge-trace-norm-other-stab-facets`. The numerics in that node put the smallest ratio of all
tested facets at the antiholes (`C̄_9`: `1.108`).

**Status by `n`** (route `hermitian-edge-trace-norm-odd-antihole-facets-by-size`):

| n | method | bound | needed `sqrt3(n-2)` |
|---|---|---|---|
| 7 | cover by 7 houses, `||house||_1 >= 6.1859` (exact SDP branch-and-bound) | 8.660260 | 8.660254 |
| 9 | cover by 9 cliques `K_4`, `c_4 >= 5.3887` (exact SDP branch-and-bound) | 12.124575 | 12.124356 |
| 11 | cover by 11 cliques `K_5`; needs `c_5 >= 7.0857` | open | 15.588457 |
| 13 | new Delsarte-type LP on `Z_13 x disc` (interval-verified) | 19.209602 | 19.052559 |
| >= 15 | cover by cliques `K_k` + the landed energy LP | exact | |

Here `c_m` is the minimum of `||C||_1` over admissible `C` on `K_m`. The numerical value of `c_5` is
`5 + sqrt5 = 7.236`, so the `n = 11` gap is a finite computation of the same kind as
`hermitian-edge-trace-norm-clique-inequality-k5`, at a higher target.

## Attempts

- 2026-09-18 (w7-078): clique covering, house covering, and a Delsarte-type kernel LP on the
  rank-one reduction. Every odd `n >= 7` is closed except `n = 11`. For `n = 11` the kernel LP reaches
  only `15.53 / 15.59` (degree 5), and uniform-matching averaging reaches about `0.93` of the target.
  The `K_5` branch-and-bound at target `7.0857` is running
  (`experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k5hilane.sh`).
