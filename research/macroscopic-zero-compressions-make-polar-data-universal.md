---
rg: 2
id: macroscopic-zero-compressions-make-polar-data-universal
kind: claim
title: Macroscopic zero compressions make polar-correction data completely universal
distinct_from:
  leakage-small-polar-compressions-obey-projective-transfer: that proves transfer when normalized generator leakage is small; this shows the macroscopic-leakage complement contains every finite unitary tuple and hence has no residual dilation rigidity.
  vanishing-codimension-compressions-obey-projective-transfer: that uses automatic small leakage from a large retained subspace; this constructs positive-density independent coordinate subspaces with maximal leakage.
  projective-commutant-transfer-for-arithmetic-pair: that remains an assertion about approximate arithmetic representations; this says the label “polar compression of an exact arithmetic representation” imposes no restriction in the macroscopic zero-compression regime.
---

**ESTABLISHED.**  Let `G` be a finitely generated residually finite group and
let `S` be a finite symmetric set of nonidentity elements.  For every
positive integer `d` and every tuple of unitaries

```text
(U_s)_(s in S) in U(d)^S,                                (MZC1)
```

there are an exact finite-dimensional representation `pi:G->U(H)` and a
rank-`d` projection `P` such that

```text
P pi(s) P=0                         for every s in S.     (MZC2)
```

Consequently each prescribed `U_s` is a unitary polar correction of the
compression `Ppi(s)P`.  For every `s`, the normalized outgoing leakage is
maximal:

```text
||(1-P)pi(s)P||_HS^2/d=1.                              (MZC3)
```

This applies to `SL_3(Z[1/2])` and any fixed presentation-generator packet.
Thus no argument can control the macroscopic-leakage branch of projective
transfer merely from the existence of an exact ambient dilation and polar
corrections: that description contains every approximate tuple, including
every possible enemy.  A surviving theorem must use small leakage,
nondegenerate singular-value overlap, a canonical polar choice with extra
incidence, or arithmetic constraints beyond the compression data.

The construction is not itself a counterexample to projective transfer.  The
arbitrary tuple in `(MZC1)` must still satisfy the arithmetic presentation
and carry the projective commutant leak.  The result proves that the ambient
polar-dilation label gives no help in finding or excluding such a tuple.

