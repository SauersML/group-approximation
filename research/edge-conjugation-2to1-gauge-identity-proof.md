---
rg: 2
id: edge-conjugation-2to1-gauge-identity-proof
kind: route
title: Compose the pullback with the relabelled action and read off the identity
target: edge-conjugation-of-2to1-constraints-is-pure-gauge
requires: []
---

One computation.  Fix `pi : A -> B`, a permutation `sigma` of `A`, and
`F : {-1,1}^A -> R`.  Recall the three definitions:

```text
(P_pi y)_a = y_{pi(a)}                 pullback of an assignment on B
F|_pi = F . P_pi                       the folded restriction
(sigma . X)_a = X_{sigma^{-1}(a)}      the action on assignments
F^sigma = F . (sigma^{-1} . )          the transformed long code
pi^sigma = pi . sigma^{-1}             the conjugated constraint
```

`F^sigma` is the transformation forced by preserving dictator completeness:
if `F` is the dictator at `a`, then `F^sigma` is the dictator at
`sigma(a)`, which is where the relabelling sends it.

Now evaluate.  Fix `y in {-1,1}^B` and set `Z = P_{pi^sigma} y`, so
`Z_a = y_{pi(sigma^{-1}(a))}`.  Then for every `a in A`,

```text
(sigma^{-1} . Z)_a = Z_{sigma(a)} = y_{pi(sigma^{-1}(sigma(a)))} = y_{pi(a)} = (P_pi y)_a,
```

so `sigma^{-1} . Z = P_pi y` identically.  Therefore

```text
(F^sigma)|_{pi^sigma}(y) = F^sigma(Z) = F(sigma^{-1} . Z) = F(P_pi y) = F|_pi(y),
```

which is `(G1)`.  Nothing about `pi` beyond being a map is used, so the
identity holds for 2-to-1, `d`-to-1 and general constraints alike; the
2-to-1 case is only where it is being applied.

The identity is an equality of functions on `{-1,1}^B`, so every functional
of the folded restriction agrees before and after conjugation: Fourier
coefficients, influences, noise stability, the acceptance probability of any
test that reads only `F|_pi`.  That is the sense in which the conjugation
is pure gauge.
