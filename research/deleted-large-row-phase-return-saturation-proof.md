---
rg: 2
id: deleted-large-row-phase-return-saturation-proof
kind: route
title: Conjugate the phase-corrected HNN word back to its order-two base clock
target: deleted-large-row-phase-return-is-finite-clock-saturated
requires: []
---

All factors in `(DLR2)` commute except for the displayed stable-letter
transport.  On `P_-`, `J=-1` and `cb=-1`.  Hence

```text
cP_-=-bP_-=JbP_-.
```

Using `a t=t c`, which follows directly from `(DLR1)`, gives

```text
a t P_-=t cP_-=t P_-Jb,
```

and right multiplication by `(Jb)^(-1)t^(-1)` proves `(DLR3)`.  The usual
commuting-involution calculation gives

```text
||c-b||_2^2=tau(2-2cb)=4 tau((1-cb)/2),
```

which is `(DLR4)` on a representation where `J=-1`; with a non-scalar
central sign the same formula holds after normalizing the `e_-` corner.

But the same substitution `a t=t c` applies before compression:

```text
u=t c(Jb)^(-1)t^(-1)=t(Jcb)t^(-1).
```

Since `J,c,b` are commuting involutions, `(Jcb)^2=1`.  This proves
`u^2=1`.  Also `v=Jcb` acts as `+1` on `P_-`, so the transported carrier is
contained in the `+1` spectral projection of `u`.

For a nonidentity involution the canonical trace of `(1+u)/2` is `1/2`.
The order-two case of `finite-clock-fejer-threshold-is-sharp` says that no
approximate fixed contraction can have asymptotic squared mass exceeding
this canonical atom.  Passing to a subsequence on which one member of a
fixed menu is selected changes neither its order nor this ceiling, proving
the finite-menu assertion.

