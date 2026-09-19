---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of the web C_n^4 for every n >= 10 except twelve values
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k4-clique-windows.md
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_k4_check.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_k4_check.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-large-k: that is k = 3 and k >= 5, with the large-m and K_4 bounds; this is k = 4, which needs the K_5 margin.
  hermitian-edge-trace-norm-odd-antihole-c11: that is C̄_11 = C_11^4 alone; this is every web C_n^4, with n = 11 among them.
---

**ESTABLISHED (ordinary proof on one computer-assisted input; exact rational arithmetic;
unreviewed, not Lean-verified; route `hermitian-edge-trace-norm-web-rank-k4-clique-windows`).**

**Theorem.** Let `C_n^4` be the web on `Z_n` with `i ~ j` iff the cyclic distance is in `1..4`. For
every `n >= 10` except

```text
n  =  12, 13, 14, 17, 18, 19, 23, 24, 28, 29, 34, 39 ,
```

every admissible `C` on `C_n^4` satisfies `||C||_1 >= sqrt3 (n - floor(n/5))`.

This is `(**)` at the rank inequality of `C_n^4`. It is a facet when `5` does not divide `n`
(`webfacet.log`, for `n <= 23`). With `hermitian-edge-trace-norm-web-rank-k2` and
`hermitian-edge-trace-norm-web-rank-large-k`, every `k >= 2` now has at most finitely many open
webs. The case `n = 11` is the antihole `C̄_11`.

## Attempts

- 2026-09-18 (w7-078): proved by clique windows with `c_5 >= 7.0857`, route
  `hermitian-edge-trace-norm-web-rank-k4-clique-windows`. With only `c_5 >= 4 sqrt3`, the windows
  prove nothing for `k = 4`, because the margin is zero.
