---
rg: 2
id: two-qutrit-controlled-bases-give-proper-multipath-marginal
kind: claim
title: Controlled two-qutrit bases give a proper noncentral multipath marginal
artifacts:
  - research/two-qutrit-proper-multipath-marginal-proof.md
distinct_from:
  one-center-heisenberg-tree-has-no-proper-escaped-marginal: that proves one-qutrit Heisenberg vertices force every context into one maximal abelian chart; this enlarges one vertex to the two-qutrit extraspecial packet and explicitly crosses that classification.
  central-type-sum-equality-is-intersection-readable: that treats one central finite chart on each side; this projection is a sum of paths from three different charts and is not itself any transported central finite type.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that absorbs single finite arrows and bisections; this is a genuine additive block entry, although the whole finite Bass--Serre host remains hyperlinear for a different reason.
---

Let `omega` be a primitive cube root. Let `K=E^(1)` be an order-`3^3`
Heisenberg group and let `F=E^(2)` be the order-`3^5` extraspecial
group

```text
F=<J,X_1,Z_1,X_2,Z_2 |
   J central, every generator has order 3,
   X_i Z_i=J Z_i X_i,
   all other displayed pairs commute>.
```

Identify their centers `Z=<J>` and form

```text
Gamma=K *_Z F,                q=e_(Z,omega)=z_(K,pi_omega). (TQM1)
```

Inside `F`, put

```text
B_0=Z_2,              B_1=X_2,              B_2=X_2 Z_2,
A_a=<J,Z_1,B_a>                                      (a in F_3).
```

For `a,b in F_3`, let `alpha_(a,b)` be the character of `A_a`
defined by

```text
alpha_(a,b)(J)=omega,
alpha_(a,b)(Z_1)=omega^a,
alpha_(a,b)(B_a)=omega^b,
p_(a,b)=z_(A_a,alpha_(a,b)).                            (TQM2)
```

The nine projections form one exact escaped context:

```text
p_(a,b)p_(c,d)=0  unless (a,b)=(c,d),
sum_(a,b) p_(a,b)=q.                                   (TQM3)
```

The three-path sum

```text
P=p_(0,0)+p_(1,0)+p_(2,0)                              (TQM4)
```

is a proper projection with

```text
tau(P)=1/9,             tau(q)=1/3.                     (TQM5)
```

It is noncentral in `q C[F] q isomorphic to M_9(C)`, and more strongly
there are no finite `H<=Gamma`, `rho in Irr(H)`, and `g in Gamma`
with

```text
P=g z_(H,rho) g^(-1).                                  (TQM6)
```

Thus `P` is genuinely a multipath-sum atom, not a renamed transported
finite type.

It gives an exact proper shared marginal between the two context PVMs

```text
C_fine={p_(a,b):a,b in F_3},
C_coarse={P,q-P}.                                      (TQM7)
```

For a shared binary variable, declare the plus outcomes of `C_fine` to
be the three labels `(a,0)` and the plus outcome of `C_coarse` to be
`P`. Their marginal identity is exactly `(TQM4)`; all projection,
orthogonality, unit, and shared-marginal equations hold in the algebraic
group corner.

This is again a positive boundary cell, not a nonhyperlinear group.
`Gamma` is an amalgam of two finite groups over a finite group, hence
virtually free and hyperlinear. The cell proves that a larger finite packet
can solve the **local** proper-multipath gate. What remains load-bearing is
to put such a cell in a finite support group whose marked type is
finite-dimensional-invisible and whose global context incidences encode the
no-CE BCS; finite Bass--Serre attachment does neither.
