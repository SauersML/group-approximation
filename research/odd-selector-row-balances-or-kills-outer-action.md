---
rg: 2
id: odd-selector-row-balances-or-kills-outer-action
kind: claim
title: One odd Whitehead selector row either balances the gauge or kills the controlled outer action
distinct_from:
  orientation-graded-mixed-returns-have-a-balanced-double: that constructs the balanced escape whenever a C2 grading survives; this treats the smallest relation that destroys that grading and shows that the escape survives internally.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that proves an identity-outer anchor with the same gauge would be sufficient; this shows that identifying the CZ implementer with one conjugated coarse Pauli reflection does not create such an anchor.
  literal-prefix-three-root-swap-retains-typed-carriers: that keeps source and target packet identities typed; this gives a same-Hilbert marked countermodel after the odd selector equality is imposed.
---

**ESTABLISHED NO-GO.**  Let `P` be the two-qubit extraspecial Pauli group
on its four-dimensional marked spin module `S`, let `C` be the fine-atom
controlled-Z reflection, and let

```text
G=P semidirect_alpha <t | t^2=1>                      (SOW1)
```

be the controlled extension.  Choose any noncentral Pauli reflection
`r in P`; on `S` it has normalized trace zero.  The smallest odd-selector
proposal adjoins a Whitehead actuator `W` and the single row

```text
t=W r W^*.                                              (SOW2)
```

This row destroys the orientation homomorphism which sends `t` to the
nontrivial element of `C_2` and sends `P,W` to zero.  Nevertheless it does
not authenticate the literal fine reflection.

## Exact balanced countermodel

On `S tensor C^2` put

```text
rho(p)=S(p) tensor I_2,
rho(t)=C tensor diag(1,-1).                              (SOW3)
```

Both `rho(r)` and `rho(t)` are self-adjoint involutions with four positive
and four negative eigenvalues.  Therefore a unitary `W` exists with

```text
rho(t)=W rho(r) W^*.                                    (SOW4)
```

This is an exact eight-dimensional marked representation of `(SOW1)--(SOW2)`
with `mu=0`.  Its Pauli and controlled Reynolds ranks remain `1/16` and
`1/32`, so `balanced-controlled-whitehead-return-checksum` leaves the full
`1/32` adjoint leakage for every attempted return.  One conjugated reflection
does not identify the two Reynolds ranges.

The approximate statement points in the same direction.  After exactifying
the finite packet, write `rho(t)=C tensor V` and let

```text
delta_W=||rho(t)-W rho(r)W^*||_2.
```

Since `tr(r)=0` and `tr(C)=1/2`, trace contractivity gives

```text
|mu|/2=|tr(rho(t))|<=delta_W,
|mu|<=2 delta_W,                                        (SOW5)
```

and hence

```text
c_P-c_G=(1-mu^2)/32
          >=(1-4 delta_W^2)/32.                         (SOW6)
```

Thus a small odd-row defect **maximizes** the superrank obstruction instead
of selecting either literal orientation.

## The normalizer repair destroys completeness

Suppose one tries to strengthen `(SOW2)` by requiring `W` to normalize the
same embedded packet `P`.  Then `WrW^*` lies in `P`, so `(SOW2)` makes the
automorphism induced by `t` on `P` inner.  But controlled-Z induces the
nontrivial outer symplectic transvection `alpha` on `P/Z(P)`.  Hence no
representation in which the marked Pauli packet remains faithful can satisfy
both the normalizer repair and `(SOW2)`.

Therefore the smallest odd selector has a sharp dichotomy:

1. without whole-packet normalization it has the exact balanced countermodel
   `(SOW3)--(SOW4)`; or
2. with whole-packet normalization it destroys the intended exact controlled
   packet and cannot serve as the infinite marked completeness model.

The surviving mixed return must be neither a single-reflection conjugacy nor
a literal normalizer of the finite Pauli group.  It must compare an averaged
Reynolds range through a self-similar/infinite coefficient coordinate, so
that the finite packet sees the checksum `(BCW6)` while the properly infinite
model retains its outer action.

Nor does replacing `r` by an involution from a larger finite marked packet
provide the missing pure anchor.
`finite-marked-involution-anchor-has-one-third-wrong-mass` proves that the
marked regular trace gives average character zero to every noncentral
involution.  At most two-thirds of its Plancherel mass can have normalized
trace `1/2`, and at least one-third therefore has the wrong controlled
orientation.  The required anchor must be genuinely infinite/type-selective
or payload-coupled, not merely a more elaborate finite word.
