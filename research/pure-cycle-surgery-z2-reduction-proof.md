---
rg: 2
id: pure-cycle-surgery-z2-reduction-proof
kind: route
title: Specialize the BS base to the identity and optimize the cutoff
target: pure-cycle-surgery-rate-contains-quantitative-z2-repair
requires:
  - flexible-bs-cycle-surgery-absorbs-exact-coboundaries
---

For `S=1`, the relation `RSR^(-1)=S^4` is automatic and the base commutant
is the full matrix algebra.  The coboundary residual is

```text
||c Ad(R)(c)^(-1)-1||_2=||[c,R]||_2.
```

The asserted output commutant condition includes `[R_0,c_0]=0`, proving the
reduction to two-unitary repair.  Balancing `K delta` with `K^(-1/2)` gives
`K` comparable to `delta^(-2/3)` and `(PCZ2)`.  Glebsky's Theorem 1 supplies
the stated unconditional `delta^(1/9)` fallback used in `(FCP6)`.
