---
rg: 2
id: d16-common-gauge-select-collapses-charger-to-payload
kind: claim
title: Common-gauge SELECT collapses the D16 charger to its payload word
distinct_from:
  hadamard-selector-commutator-charges-two-path-leakage: that computes a positive HS charge once two diagonal blocks of a selector-central word are available; this proves that the natural ordinary conjugacy relation producing the desired relative block also identifies the charger with the payload in the abstract group.
  finite-cocycle-select-has-an-exact-power-return: that gives a hostile finite-dimensional return caused by the finite cocycle controller; this is a group-normal-form collapse of the phase-twisted D16 wandering candidate, independent of compressed powers.
  deleted-large-row-phase-return-is-finite-clock-saturated: that treats an HNN row which is a conjugate of a commuting finite-order product; this treats the common-orientation SELECT controller and shows its transverse Hadamard commutator is literally the finite-order payload.
---

**ESTABLISHED NO-GO.**  Let `z,h,x,c,r` be group elements satisfying

```text
z^2=h^2=x^2=r^2=1,
x=h z h,
c x c^(-1)=r x,
[r,h]=1.                                                (DGC1)
```

The last two relations are precisely the binary common-gauge SELECT
covariance: on the selected `z`-packet, the controller `c` has blocks

```text
diag(A,rA)                                               (DGC2)
```

with one arbitrary common right gauge `A`.  The tempting transverse charger

```text
g=[h c h,z]                                             (DGC3)
```

does cancel that gauge and evaluates as two copies of `r` on the intended
packet.  But it is not wandering.  It satisfies the exact abstract identity

```text
g=r.                                                     (DGC4)
```

Indeed, using the commutator convention `[a,b]=aba^(-1)b^(-1)` and the
involution relations,

```text
h g h
 =c (h z h)c^(-1)(h z h)
 =c x c^(-1)x
 =(r x)x
 =r.
```

Since `[r,h]=1`, conjugating back gives `(DGC4)`.

Consequently adjoining a central involution `J` and phase-twisting to

```text
u=J[h c h,z]                                            (DGC5)
```

does create an exact fixed carrier on the `J=-1,r=-1` sector, but

```text
u=Jr,
```

so `u` has order at most two when `J` and `r` commute.  Its fixed carrier is
contained in the canonical trivial-character atom of that finite clock and
cannot pass the Fejer threshold by
`finite-clock-fejer-threshold-is-sharp`.

## Application to coherent verifier wordization

For `K=C_2`, `finite-cocycle-select-forces-one-common-lcu-gauge` uses a
shift `x` and the relation

```text
c x c^(-1)x^(-1)=r.                                    (DGC6)
```

The D16/Hadamard packet supplies `x=hzh`.  Thus `(DGC6)` is exactly `(DGC1)`.
On the natural two-dimensional type, a direct block computation gives

```text
[h diag(A,rA) h,z]=diag(r,r),                           (DGC7)
```

but `(DGC4)` shows that this is not a matrix-only promotion: the same equality
already holds in the group.

This closes the most direct robust repair of
`fanizza-coherent-verifier-wandering-promotion`.  The construction avoids
independent multiplicity gauges and couples the controller to the payload,
so it is not defeated by the sofic exact-finite-dimensional-invisibility
wrapper.  Instead it overcouples them: the relation that authenticates the
relative verifier block removes the stable normal form needed for wandering.

A surviving two-cell must therefore enforce the relative block only on a
model-dependent positive carrier, or infer it from a finite-dimensional-only
payload inequality.  A literal common-gauge conjugacy equation cannot do so.

