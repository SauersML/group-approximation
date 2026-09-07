---
rg: 2
id: leavitt-unit-max-mf-quotient-proof
kind: route
title: The graph K-theory sequence at the rose with n petals
target: leavitt-unit-max-mf-quotient-is-power-cokernel
requires:
  - purely-infinite-unit-group-max-mf-quotient-is-k1
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

## Why sufficient

`L_k(1,n)` is purely infinite simple for `n >= 2`, which is
Ara--Goodearl--Pardo Theorem 4.2 for `V_(1,n)`, so the classification
applies and the maximal MF quotient is `K_1(L_k(1,n))`.

Ara--Brustenga--Cortinas Corollary 7.7, quoted, for `k` a principal ideal
domain, and a field is one:

```text
K_1(L_k(E)) = coker(1-N^t : K_1(k)^(E_0 minus Sink) -> K_1(k)^(E_0))
              (+) ker(1-N^t : Z^(E_0 minus Sink) -> Z^(E_0)).
```

The graph is one vertex with `n` loops, fixed by the manuscript's own
presentation with `n` generators `s_i` summing to `1`, so `N = (n)` and
`1-N^t` is multiplication by `1-n`.  On `Z` that is injective for `n >= 2`,
so the kernel term vanishes.  On `K_1(k) = k^x`, written multiplicatively, it
is the `(1-n)`-th power map, whose cokernel is `k^x/(k^x)^(n-1)`.

The table entries follow: `n = 2` gives the trivial group; `F_2^x = 1` gives
the trivial group for every `n`; `F_q^x` is cyclic of order `q-1`, so its
quotient by `(n-1)`-th powers is cyclic of order `gcd(q-1,n-1)`; and `n = 3`
over `Q` gives `Q^x/(Q^x)^2`.
