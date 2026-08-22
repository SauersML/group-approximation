---
rg: 2
id: controlled-fine-reflection-superrank-orientation-proof
kind: route
title: Decompose the two controlled-reflection extensions and compute both commutants
target: controlled-fine-reflection-superrank-orientation-law
requires:
  - controlled-pauli-corner-has-clifford-groupification
  - weyl-commutant-superrank-detects-rectangular-return
  - reynolds-rank-gap-forces-hs-holonomy-energy
---

By the controlled-Z representation classification, every marked
representation is `(CFS2)`.  The Pauli algebra is

```text
M_4(C) tensor I_k,
```

so its commutant is `I_4 tensor M_k(C)` and has dimension `k^2`.  Since
`dim H_-=4k`, this gives `c_P=1/16`.

Adjoining `t=C tensor V` is equivalent, after multiplying analytically by
`C tensor I` from the Pauli algebra, to adjoining `I tensor V`.  Therefore
the commutant of the full controlled-reflection group is

```text
I_4 tensor (M_(k_+)(C) direct_sum M_(k_-)(C)),
```

of dimension `k_+^2+k_-^2`.  With

```text
k_+^2+k_-^2
 =((k_++k_-)^2+(k_+-k_-)^2)/2
 =k^2(1+mu^2)/2,
```

division by `(4k)^2` proves `(CFS4)`.

If only one sign occurs, the represented algebra is `M_4(C)`.  If both
occur, it is `M_4(C) direct_sum M_4(C)`.  Polynomial identities of a direct
sum are the intersection of the identities of its summands, hence in both
cases the PI ideal is `Id(M_4(C))`.  This proves the standard-polynomial
blindness claim.

For `(CFS5)`, use the explicit group-algebra formula

```text
C=(I-c)+cZ_2,             c=(I-Z_1)/2.
```

Every support term of `tC` belongs to `tP`.  The supports of `qtC` belong
to `tP` as well because `J` lies in `P`.  The stable-letter coset is
disjoint from the identity in the semidirect product, so the canonical
coefficient of the identity is zero.  Normalizing by the positive trace of
`q` proves `(CFS5)`, hence `mu=0` and `(CFS6)`.

Finally, finite-group flexible HS exactification transfers the exact
isotypic calculation to sufficiently accurate packet microstates.  The
rank gap itself can be compared under a returned adjoint holonomy by
`reynolds-rank-gap-forces-hs-holonomy-energy`; no tracial analogue of the
finite matrix-space rank comparison is asserted.
