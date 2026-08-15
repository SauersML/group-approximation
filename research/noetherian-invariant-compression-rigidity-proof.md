---
rg: 2
id: noetherian-invariant-compression-rigidity-proof
kind: route
title: Iterate the compression and terminate the chain
target: noetherian-invariant-compression-rigidity
requires: []
---

## Direct proof

Monotone case.  `s L s^{-1} <= L` and monotonicity give
`I(s L s^{-1}) <= I(L)`, which by equivariance reads `s . I(L) <= I(L)`.
Applying the order-automorphism `p -> s^k . p` yields

```text
I(L)  >=  s . I(L)  >=  s^2 . I(L)  >=  ... ,
```

a descending chain.  The chain condition gives `k` with
`s^(k+1) . I(L) = s^k . I(L)`; applying `p -> s^(-k) . p` gives
`s . I(L) = I(L)`.  Then for every `k >= 0`, equivariance gives
`I(s^k L s^(-k)) = s^k . I(L) = I(L)`.

Antitone case.  The same two lines with the ascending chain
`I(L) <= s . I(L) <= s^2 . I(L) <= ...` and the ascending chain
condition.
