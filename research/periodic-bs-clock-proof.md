---
rg: 2
id: periodic-bs-clock-proof
kind: route
title: Use finite doubling permutations and count their fixed points
target: periodic-bs-clock-defeats-spectral-first-hit-checksum
requires: []
---

Write `r=2^(-1) mod q`.  Since `P_q^(-1)e_x=e_(2x)`, direct evaluation gives

```text
P_q Z_q P_q^(-1)e_x=zeta^(2x)e_x=Z_q^2e_x,
```

which proves the exact relator.

For `q` prime,

```text
tr(Z_q^k)=0                                           (PP1)
```

whenever `q` does not divide `k`.  The matrix `P_q^k` is a permutation
matrix.  Its fixed points solve

```text
(2^k-1)x=0 mod q,
```

so

```text
tr(P_q^k)=gcd(2^k-1,q)/q.                             (PP2)
```

Choose a prime `q_n>2^n`.  For `1<=k<=n`, `(PP1)` is zero and `(PP2)` is
`1/q_n`.  Negative moments are complex conjugates, so this proves weak
convergence of both marginal spectral measures to Haar measure.

For the cross overlap,

```text
tr(P_q^* Z_q)
 =(1/q) sum_x zeta^x <e_x,e_(2x)>
 =1/q,                                                (PP3)
```

because `2x=x mod q` has only the solution `x=0`.  Therefore

```text
||P_q-Z_q||_2^2
 =2-2 Re tr(P_q^*Z_q)
 =2-2/q.
```

The spectral projections `E_x` of `Z_q` obey

```text
P_q E_x P_q^*=E_(rx).
```

The order of `2 mod q_n` is greater than `n`: an order at most `n` would
make `q_n` divide a positive integer `2^k-1<q_n`.  Hence the orbit of any
nonzero atom has more than `n` distinct points.  Taking one atom as the
challenge set gives `n` disjoint one-dimensional first-hit projections.
For arbitrary unitaries `U,V` and any such projection `E`,

```text
||(U-V)E||_2^2<=4 tr(E)=4/q_n.                        (PP4)
```

The permutation is finite, so every orbit either eventually hits the
challenge atom and then repeats, or is a periodic orbit disjoint from it.
There is no dissipative tail.  Equations `(PP1)--(PP4)` prove the claim.

