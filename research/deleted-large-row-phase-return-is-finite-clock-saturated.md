---
rg: 2
id: deleted-large-row-phase-return-is-finite-clock-saturated
kind: claim
title: The phase-corrected large deleted row returns only a saturated order-two clock
distinct_from:
  deleting-one-gap-row-has-the-wrong-orientation: that proves a deleted consistency row has large finite-dimensional defect; this accepts that lower bound and computes the phase-corrected HNN return it supplies.
  finite-clock-fejer-threshold-is-sharp: that treats an arbitrary finite-order word and contraction; this identifies the proposed deleted-row carrier as a subprojection of the exact trivial character of an order-two conjugate.
  heterogeneous-britton-row-has-regular-energy-floor: that treats an HNN word whose row is not a defining edge conjugacy and proves a positive regular energy floor; here setting c=t^(-1)at makes the prospective word a conjugate of a base involution and destroys Britton wandering.
---

**ESTABLISHED NO-GO.**  Let `J,c,b` be commuting involutions with `J`
central, and suppose an HNN stable letter is used to define

```text
c=t^(-1) a t.                                         (DLR1)
```

Put

```text
e_-=(1-J)/2,
P_-=e_-(1-cb)/2,
u=a t (Jb)^(-1)t^(-1).                                (DLR2)
```

The proposed sign reversal is an exact local identity:

```text
cP_-=JbP_-,
(u-1)tP_-=0.                                          (DLR3)
```

Moreover, on the negative central sector,

```text
tau((1-cb)/2)=||c-b||_2^2/4.                          (DLR4)
```

Thus a large deleted consistency defect really does produce a large fixed
carrier.  It does not, however, produce a wandering word.  From `(DLR1)`,

```text
u=t v t^(-1),             v=c(Jb)^(-1)=Jcb,           (DLR5)
v^2=1,
Q:=tP_-t^(-1) <=(1+u)/2.                              (DLR6)
```

Equivalently `u^2=1` in the abstract group.  If `v!=1`, its canonical
regular `+1` spectral projection has trace exactly `1/2`; every returned
carrier for `u` has mass at most this value.  This is exactly the sharp
order-two ceiling in `finite-clock-fejer-threshold-is-sharp`.  If `v=1`,
then `u=1` and there is no marked word at all.

Consequently a finite menu of deleted rows does not help.  Each successful
menu entry may depend on the microstate, but every entry is an order-two
clock and its fixed carrier is bounded by its canonical trivial-character
mass.  Finite-menu pigeonholing preserves the same threshold; it cannot turn
these conjugated edge rows into the infinite-order carriers required by the
Fejer contradiction.

The obstruction survives the evident higher-order variant.  If commuting
finite-order letters replace `c,b,J`, then `(DLR5)` is conjugate to their
commuting finite-order product.  A carrier on which their phases match lies
inside one spectral atom of that finite clock, at no more than the
corresponding canonical character mass.  Exceeding that mass requires an
additional matrix-only replication or a noncommuting/wandering factor, which
is not supplied by the deleted-row gap.
