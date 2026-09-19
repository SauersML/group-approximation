---
rg: 2
id: hs-defect-operator-norm-quarantine-proof
kind: route
title: Cut the joint defect-energy operator at a spectral threshold
target: hs-defect-operator-norm-quarantine
requires: []
---

Form the positive operator

```text
H = sum_i (D_i^* D_i + D_i D_i^*).
```

Its normalized trace is

```text
tau(H)=2 sum_i ||D_i||_2^2=2E.
```

Let

```text
r = 1_[eta^2,infinity)(H),
q = 1-r.
```

Markov's inequality in the spectral calculus gives

```text
tau(r) <= tau(H)/eta^2 = 2E/eta^2.
```

Because `q` is a spectral projection of `H`, it commutes with `H` and

```text
q H q <= eta^2 q.
```

For each `i`, positivity gives both

```text
D_i^* D_i <= H,
D_i D_i^* <= H.
```

Hence

```text
q D_i^* D_i q <= eta^2 q,
q D_i D_i^* q <= eta^2 q.
```

Taking operator norms and using

```text
||D_i q||_op^2 = ||q D_i^* D_i q||_op,
||q D_i||_op^2 = ||q D_i D_i^* q||_op
```

yields

```text
||D_i q||_op <= eta,
||q D_i||_op <= eta.
```

The two-sided compression satisfies

```text
||q D_i q||_op <= min(||D_i q||_op,||q D_i||_op) <= eta.
```

If every `||D_i||_2<=delta`, then `E<=N delta^2`, giving the stated packet
bound.  Substituting `eta=sqrt(delta)` gives
`tau(1-q)<=2N delta` and operator-norm defect at most `sqrt(delta)`.

Nothing in the construction relates `q` to the model unitaries, so no
invariance or compressed multiplicativity statement follows.  The warning in
the target is therefore part of the proved scope, not an omitted estimate.
