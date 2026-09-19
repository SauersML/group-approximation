---
rg: 2
id: contractive-computation-ladder-proof
kind: route
title: Iterate the recursion and sum a polynomial against a geometric series
target: contractive-computation-ladder
requires: []
---

Iterating `(CCL1)` to depth `N` gives

```text
a_0 <= lambda^N a_N + C sqrt(E) sum_(n=0)^(N-1) lambda^n p(n).
```

Since `a_N` is uniformly bounded and `0 < lambda < 1`, the first term tends to
`0` as `N -> infinity`.  The series `sum_n lambda^n p(n)` converges for every
fixed polynomial `p`, because exponential decay dominates polynomial growth;
explicitly, if `p` has degree `k` then `sum_n lambda^n n^k` is finite and equals
a fixed rational function of `lambda`.  Letting `N -> infinity` gives `(CCL2)`,
and `(CCL3)` is `(CCL2)` rearranged under `a_0 >= a_*`.

**Positive-density version.**  Let `S` be the set of levels carrying the factor
`lambda`, of lower density `eta`.  Iterating gives

```text
a_0 <= ( prod_(n<N, n in S) lambda ) a_N
        + C sqrt(E) sum_(n<N) ( prod_(j<n, j in S) lambda ) p(n),
```

and `prod_(j<n, j in S) lambda = lambda^(|S cap [0,n)|) <= lambda^(eta n + o(n))`
by the definition of lower density.  The same two observations apply: the first
term vanishes and the series converges.
