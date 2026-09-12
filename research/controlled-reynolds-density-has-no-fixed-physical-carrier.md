---
rg: 2
id: controlled-reynolds-density-has-no-fixed-physical-carrier
kind: claim
title: The controlled Reynolds density cannot be internalized by one fixed physical carrier
distinct_from:
  schur-density-gap-has-no-direct-relator-certificate: that rules out relator-ideal payment of a nonzero packet projection; this rules out representing the adjoint commutant density by any fixed physical group-algebra coefficient, even before asking for a relator certificate.
  balanced-controlled-whitehead-return-checksum: that expresses the adjoint return by trace squares and gives its 1/32 leakage; this explains why the trace-square level cannot be replaced by one ordinary matrix carrier.
  odd-selector-row-balances-or-kills-outer-action: that refutes one conjugated reflection row; this gives the direct-sum obstruction for every fixed physical projection or positive coefficient.
---

**ESTABLISHED.**  Let `G=P semidirect <t>` be the controlled two-qubit
Pauli group and let `rho_+,rho_-` be its two four-dimensional marked spin
representations,

```text
rho_+(t)=C,                 rho_-(t)=-C.                (CRD1)
```

For a marked representation `rho`, write

```text
c_G(rho)=rank(R_G(rho))/dim(rho)^2                     (CRD2)
```

for the normalized adjoint Reynolds rank.  The orientation law gives

```text
c_G(rho_+)=c_G(rho_-)=1/16,
c_G(rho_+ direct_sum rho_-)=1/32.                      (CRD3)
```

Let `E` be any fixed matrix-valued group-algebra element (a projection or
positive contraction is the intended case), and normalize its physical
matrix trace after evaluation.  Then

```text
tr_(rho_+ direct_sum rho_-)(E)
  =(tr_(rho_+)(E)+tr_(rho_-)(E))/2.                    (CRD4)
```

Consequently it is impossible to have

```text
|tr_rho(E)-c_G(rho)|<1/64                              (CRD5)
```

simultaneously for the three representations in `(CRD3)`.  Indeed the first
two estimates put the right side of `(CRD4)` within `1/64` of `1/16`, while
the third puts the same number within `1/64` of `1/32`; their target values
are `1/32` apart.  The weak bound `<=1/64` is sharp for this three-point
test.

The same affine obstruction applies to every finite sum of ordinary
normalized-HS word energies: evaluation on a direct sum is the dimension-
weighted average of the energies on its summands.  In contrast, adjoint
commutant rank contains squares of multiplicities and drops when inequivalent
orientation types are mixed.

Therefore a genuinely nonnormal/self-similar Whitehead actuator cannot turn
the fixed `1/32` superrank gap into one **pre-existing physical projection**
or one representation-independent group-algebra carrier.  It must instead
do one of two harder things:

1. control the quadratic trace-square checksum of
   `balanced-controlled-whitehead-return-checksum` directly; or
2. make at least one of `rho_+,rho_-` fail to extend through the same odd
   cell, so their balanced direct sum is unavailable.

This is the precise extension-selection burden for an odd row intended to
pay an affine/Fano forbidden projection.  If both literal orientations
extend with zero row energy, every ordinary row also has zero energy on their
balanced direct sum, exactly where the `1/32` Reynolds obstruction appears.
Self-similarity and nonnormality alone do not change this affine direct-sum
fact.

A finite auxiliary packet cannot furnish the missing type selection by one
better-chosen involution.  `finite-marked-involution-anchor-has-one-third-wrong-mass`
shows that every noncentral finite-packet involution has marked Plancherel
average trace zero; at least one-third of the marked mass fails the
trace-`1/2` condition needed to conjugate it to the pure controlled
reflection.  The remaining option is therefore genuinely infinite or
payload-coupled extension selection.
