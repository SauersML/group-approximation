---
rg: 2
id: bounded-abelian-register-spectral-loss-proof
kind: route
title: Pair joint eigenvalues inside a torus grid
target: bounded-abelian-register-has-polynomial-spectral-loss
requires: []
artifacts:
  - research/artifacts/bounded-abelian-register-spectral-loss-2026-08-21.md
---

Put `M=floor((N/2)^(1/k))`.  The size hypothesis gives `M>=2`,
`M^k<=N/2`, and `M>=(N/2)^(1/k)/2`.  Partition each circle into `M`
half-open angular arcs and hence the joint spectrum into at most `M^k`
boxes.  Pair coordinates inside each occupied box.  If the occupancies are
`n_b`, the number of pairs satisfies

```text
P=sum_b floor(n_b/2)>=(N-M^k)/2>=N/4.
```

Let `S` swap each pair and fix the unpaired coordinates.  Its diagonal is
the normalized-Hilbert--Schmidt projection onto `D_N`, so
`dist_2(S,D_N)^2=2P/N>=1/2`.  Within a box every coordinate eigenvalue is at
chord distance at most `2pi/M`.  Each pair contributes two such commutator
entries, whence

```text
sum_i ||[S,U_i]||_2^2
 <=4pi^2 k/M^2
 <=16pi^2 k(2/N)^(2/k).
```

If two joint labels coincide, their off-diagonal matrix unit commutes with
every `U_i`, so the generated diagonal algebra is already strictly smaller
than `D_N`.  This proves both alternatives.
