---
rg: 2
id: leavitt-regular-atlas-separating-refinement-proof
kind: route
title: Carry a finite separation window through finite-factor regularization
target: leavitt-regular-atlas-separating-refinement
requires: [leavitt-regular-atlas-hyperlinearity-criterion]
artifacts:
  - docs/EXPLICIT_LEAVITT_ATLAS.md
---

Start the forward proof of the canonical regular-atlas criterion with a
trace-preserving hyperlinear embedding of `Q`, but choose the finite window to
contain not only the two finite factors and `bar_S` but also every word in the
fixed set `W`.

Pull the model back to `bar_P`.  Since `bar_rho(w)!=1` for `w in W`, the group
trace of `bar_rho(w)` is zero.  Hence before regularization

```text
tau(pi_n(w)) -> 0,
||pi_n(w)-1||_2^2 = 2-2 Re tau(pi_n(w)) -> 2.
```

The proof of `leavitt-regular-atlas-hyperlinearity-criterion` then corrects
each finite-factor restriction and replaces it by regular blocks on a
`1-o(1)` fraction of the space.  That proof explicitly changes **every fixed
free-product word** by `o(1)` in normalized Hilbert--Schmidt norm.  Because
`W` is finite, carry it through the same replacement simultaneously with
`bar_S`.

Normalized trace is `L2`-Lipschitz:

```text
|tau(A)-tau(B)| <= ||A-B||_2.
```

Therefore the replacement preserves the zero-trace limit on each `w in W`,
and the distance-to-identity limit remains `sqrt(2)`.  The resulting models
have the canonical single-relative-unitary form and satisfy all claimed
limits.
