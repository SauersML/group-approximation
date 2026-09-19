---
rg: 2
id: one-sided-leavitt-overlap-payment-proof
kind: route
title: Expand the finite-trace projection distance and insert the native prefix partial swap
target: one-sided-leavitt-connector-has-sharp-overlap-payment
requires: []
---

For projections `P<=Q` and a unitary `U`, traciality gives

```text
||UQU^*-P||_2^2
 = tau(UQU^*)+tau(P)-2 Re tau(PUQU^*)
 = tau(Q)+tau(P)-2 tau(PUQU^*).
```

Since `0<=P<=1` and `UQU^*` is a projection,
`tau(PUQU^*)=tau((UQU^*)P(UQU^*))<=tau(P)`.  Therefore the last display is
at least `tau(Q)-tau(P)=tau(Q-P)`.  Taking `U=1` proves sharpness.  Also

```text
U(1-2Q)U^*(1-2P)-1=2(P-UQU^*)(1-2P),
```

and right multiplication by the unitary `1-2P` preserves the `2`-norm,
which proves `(OLC2)`.

For `(OLC3)`, prefix cancellation gives

```text
yx=s_0(t_(00)s_(00))t_0=s_0t_0=Q,
xy=s_(00)(t_0s_0)t_(00)=s_(00)t_(00)=P.
```

Using `x=PxQ`, `y=QyP`, `xy=P`, and `yx=Q`, direct multiplication gives
`J_x^2=1` and sends the second-block `Q` corner to the first-block `P`
corner.  The displayed factorization into three elementary roots is the
standard characteristic-two partial swap.  Composing with the fixed
two-block swap returns the target to the same block.  All of these are exact
identities in the Leavitt elementary group, so they survive in its exact
properly infinite marked model.

The proof intentionally stops before replacing `P,Q` by spectral
projections of approximate packet words.  That replacement is the remaining
fine-support authentication problem, not part of the projection inequality.

