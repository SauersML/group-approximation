---
rg: 2
id: scalar-reynolds-cb-norm-is-the-infinity-norm
kind: claim
title: The scalar Reynolds Green cb norm is exactly its ordinary infinity norm
distinct_from:
  constrained-reynolds-column-has-a-diagonal-scalar-shadow: that extracts the scalar signed-incidence column and states the necessary cb estimate; this removes the apparent matrix-amplification issue for that scalar restriction.
  passive-iwahori-off-zero-cb-normal-splitting: that asks for a completely bounded inverse on the full noncommutative tangent space; this applies only to the reducing diagonal scalar shadow.
---

**ESTABLISHED.**  Let `C_Q` be the scalar column in `(DSS3)` and give its
domain, codomain, kernel complement, and range the operator-space
structures inherited from the corresponding diagonal masas.  Then

```text
||(C_Q|_(ker C_Q)^perp)^dagger||_cb
 = ||(C_Q|_(ker C_Q)^perp)^dagger||_(infinity -> infinity). (SCB1)
```

Indeed every subspace of a commutative `C*`-algebra has the minimal
operator-space structure.  The Moore--Penrose inverse is a bounded map

```text
ran(C_Q) subset l_infinity(Q) (+) l_infinity(Q)
   -> (ker C_Q)^perp subset l_infinity(Q/<R>).           (SCB2)
```

Its target is minimal.  By the defining mapping property of `MIN`, every
bounded map from an arbitrary operator space into that target is completely
bounded with the same norm.  Applying this to `(SCB2)` proves `(SCB1)`;
the matrix-valued maps in `(DSS4)` are exactly its amplifications.

Consequently the diagonal necessary condition `(DSS5)` is an ordinary
uniform `l_infinity` Green estimate.  Matrix amplification introduces no
additional obstruction on this commutative reducing sector.  This does
not simplify the full passive Jacobian: its off-diagonal target is not a
minimal operator space, so the full gate in `(EPJ7)` remains genuinely
completely bounded.

