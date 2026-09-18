---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k2
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of every web C_n^2 with n >= 8
artifacts:
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/README.md
  - research/hermitian-edge-trace-norm-web-rank-k2-windows.md
distinct_from:
  hermitian-edge-trace-norm-other-stab-facets-non-antihole: that is every non-clique, non-hole, non-antihole facet; this is the rank facets of the webs C_n^2 only.
  hermitian-edge-trace-norm-odd-antihole-facets: that is the antiholes, which are the webs C_n^k with n = 2k + 3; for k = 2 that is only C_7^2, which this claim excludes.
---

**ESTABLISHED (computer-assisted; the certificate is checked in exact rational arithmetic;
unreviewed, not Lean-verified; route `hermitian-edge-trace-norm-web-rank-k2-windows`).**

Let `n >= 8` and let `C_n^2` be the square of the cycle: vertices `Z_n`, with `i ~ j` iff the cyclic
distance of `i` and `j` is `1` or `2`. Its stability number is `floor(n/3)`. Then every admissible
`C` on `C_n^2` (Hermitian, zero on the diagonal and on non-edges, `|C_ij| >= 1` on edges) satisfies

```text
|| C ||_1  >=  sqrt3 ( n - floor(n/3) ) .
```

**Why it matters.** When `3` does not divide `n`, the rank inequality `x(V) <= floor(n/3)` is a
full-support facet of `STAB(C_n^2)` (Trotter 1975; `webfacet.log` checks it by the rank of the
maximum stable sets for `n <= 19`). This claim is `(**)` at that facet. So it proves an infinite
family of the facets in `hermitian-edge-trace-norm-other-stab-facets-non-antihole`, the first
outside the antiholes. For `n = 7`, `C_7^2` is the antihole `C̄_7`, which
`hermitian-edge-trace-norm-odd-antihole-facets-by-size` handles. When `3 | n` the inequality also
holds, but it is not a facet.

**Numerics** (`gmin.py`, local minimisation, not part of the proof). The minima are
`c(C_8^2) = 12.00`, `c(C_10^2) = 15.10` and `c(C_11^2) = 17.10`. Their ratios to the bound are
`1.155`, `1.245` and `1.234`.

## Attempts

- 2026-09-18 (w7-078): proved by windows of six consecutive vertices, route
  `hermitian-edge-trace-norm-web-rank-k2-windows`. An earlier and narrower certificate covered only
  `C_8^2`, by the eight rotations of `V - {x, x+3}`. It certified `c(C_8^2 - {0,3}) >= 7.7943` in
  351 boxes (log not kept). The windows supersede it.
