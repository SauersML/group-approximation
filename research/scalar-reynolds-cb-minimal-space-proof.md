---
rg: 2
id: scalar-reynolds-cb-minimal-space-proof
kind: route
title: Apply the defining mapping property of minimal operator spaces
target: scalar-reynolds-cb-norm-is-the-infinity-norm
requires: []
---

The scalar Reynolds column and its Moore--Penrose inverse are maps between
subspaces of diagonal masas:

```text
(C_Q|(ker C_Q)^perp)^dagger:
  ran(C_Q) subset l_infinity(Q) (+) l_infinity(Q)
    -> (ker C_Q)^perp subset l_infinity(Q/<R>).
```

Every operator subspace of a commutative C*-algebra carries the minimal
operator-space structure.  In particular the target above is minimal.  By
the defining mapping property of `MIN`, every bounded map from an arbitrary
operator space into this target is completely bounded with exactly the same
norm.  Applying that property to the displayed Moore--Penrose inverse gives

```text
||(C_Q|(ker C_Q)^perp)^dagger||_cb
 = ||(C_Q|(ker C_Q)^perp)^dagger||_(infinity -> infinity),
```

which is the claimed scalar Reynolds norm identity.
