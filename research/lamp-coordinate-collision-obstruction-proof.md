---
rg: 2
id: lamp-coordinate-collision-obstruction-proof
kind: route
title: One second moment
target: lamp-coordinate-collision-obstruction
requires: []
artifacts:
  - research/artifacts/hyperlinear-q34-literature-2026-08-18.md
---

## Direct proof

In `L(⊕_Y F_2)` the canonical unitaries are indexed by finitely supported
`F_2`-vectors, `u_x u_y = u_{x+y}`, and the canonical trace is `1` at the
identity and `0` elsewhere.  For `x ≠ y` the vector `δ_x + δ_y` is nonzero,
so `τ(u_x u_y) = 0`.  (For the Bernoulli picture: `u_x` is the `x`-th
coordinate function on `{−1,1}^Y` with the product measure, and the integral
of `u_x u_y` is `0` by independence and centredness.)

If a model represents `u_x` and `u_y` by the same self-adjoint unitary `v` —
which is what `p(x) = p(y)` means — then it represents `u_x u_y` by
`v² = 1`, of normalized trace `1`.  Hence the model's second moment differs
from the true one by `1`.  Since for self-adjoint unitaries

```text
‖a − b‖₂² = 2 − 2τ(ab)   and   |τ_model(w) − τ(w)| ≤ ‖·‖₂-error,
```

the discrepancy is an absolute constant in the normalized Hilbert--Schmidt
metric and cannot be made small by any choice of dimension.  Injectivity of
`p` on the tested window is therefore necessary, and it is also visibly
sufficient for the second moments, since distinct coordinates in `Y'` give
`τ(v_{p(x)}v_{p(y)}) = 0`.
