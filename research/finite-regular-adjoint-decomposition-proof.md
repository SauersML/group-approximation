---
rg: 2
id: finite-regular-adjoint-decomposition-proof
kind: route
title: Decompose conjugation on matrix units into free diagonal orbits
target: finite-regular-adjoint-retains-full-conductor
requires: []
---

On the Hilbert--Schmidt matrix-unit basis of `End(ell^2(Q))`,

```text
Ad(lambda_Q(g)) E_(x,y)=E_(gx,gy).                    (1)
```

The diagonal left action on `Q x Q` is free.  Its orbits are indexed by the
invariant `x^(-1)y`, so there are `|Q|` orbits and each is a copy of the left
regular `Q`-set.  This proves `(FRA1)`.

If `g!=1`, the free action fixes no matrix unit.  Hence the normalized trace
of `Ad(lambda_Q(g))` is zero, and the unitary identity

```text
||W-1||_2^2=2-2 Re tr(W)
```

gives `(FRA2)`.  A nontrivial element of any reduction kernel is still a
nonidentity element of `Q_a`, so the stated conductor consequence follows.
