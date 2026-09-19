---
rg: 2
id: e6-llp-two-orbit-fibre-proof
kind: route
title: Pair the six central Fourier fibres by half shift and cocycle inversion
target: e6-llp-reduces-to-base-plus-one-odd-fibre
requires:
  - metaplectic-half-shift-preserves-twisted-fibre-llp
  - twisted-c-star-opposite-inverts-cocycle
---

Fourier decomposition of the central `Z/6` gives

```text
C^*(E_6) = A_0 (+) A_(1/6) (+) A_(2/6) (+) A_(3/6)
                (+) A_(4/6) (+) A_(5/6).
```

LLP holds for a finite direct sum exactly when it holds for every summand:
coordinate projections are ucp retracts, and local lifts of finitely many
coordinates assemble blockwise.

By `metaplectic-half-shift-preserves-twisted-fibre-llp`, adding `1/2` preserves
LLP, so it pairs

```text
0 <-> 3/6,       1/6 <-> 4/6,       2/6 <-> 5/6.
```

By `twisted-c-star-opposite-inverts-cocycle`, negating the parameter also
preserves LLP.  Negation pairs `1/6` with `5/6` and `2/6` with `4/6`.
Consequently the six parameters have exactly two LLP orbits:

```text
{0,3/6}  and  {1/6,2/6,4/6,5/6}.
```

This proves the first equivalence in `(E6L1)`.  Since `2/6=1/3`, the same
orbit calculation proves the second.
