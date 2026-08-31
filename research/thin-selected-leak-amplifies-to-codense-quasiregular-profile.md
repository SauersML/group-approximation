---
rg: 2
id: thin-selected-leak-amplifies-to-codense-quasiregular-profile
kind: claim
title: Every selected thin leak tensor-amplifies to a proper co-dense quasiregular coefficient profile
distinct_from:
  full-hnn-regularity-is-a-quasiregular-unitary-orbit: that obtains the entire orthonormal quasiregular stable-letter frame from canonical HNN moments; this extracts only the base-coset coefficient from an arbitrary selected leak, with no canonical-character assumption.
  sofic-thin-coset-action-refutes-selected-profinite-continuity: that starts from a permutation atlas for the fixed action A on A/C and builds a leak; this starts from any leak and obtains an HS-approximable quasiregular profile for a possibly larger stabilizer H containing C.
  subgroup-indicators-are-diluted-hs-coefficients: that realizes 1_H for an arbitrary subgroup with no leak; the present claim's nontrivial content is the proper intermediate stabilizer H extracted from the selected leak.
---

Let `A=SL_3(Z)` and `C=<a,b>` be the explicit thin co-dense pair. Suppose
an asymptotic matrix representation induces

```text
pi:A->U(M_omega),  alpha=Ad pi,
```

and that `v in U(M_omega)` centralizes `pi(C)` but is not fixed by all of
`alpha(A)`. Define its stabilizer

```text
H={g in A: alpha(g)v=v}.                               (QRA1)
```

Then `C<=H<A`; in particular `H` is proper and profinitely dense in
`A`. Moreover there are finite-dimensional normalized-HS asymptotic
representations `beta_n` of `A` and unit vectors `xi_n` such that

```text
<beta_n(g)xi_n,xi_n> -> 1_H(g)        for every g in A. (QRA2)
```

The right side is the base-coset coefficient of the quasiregular
representation `lambda_(A/H)`.

The implication from the selected leak to `C<=H<A` is the substantive
part. The scalar conclusion `(QRA2)` alone is automatic for this `H`,
and indeed for every subgroup, by
[[subgroup-indicators-are-diluted-hs-coefficients]]. Thus `(QRA2)` must
not be counted as progress toward a sofic atlas unless additional
matrix-origin provenance is stated as mathematical data rather than only
in prose.

The remaining root
[[thin-quasiregular-profile-promotes-to-liftable-charts]] is therefore the
bare assertion that every proper intermediate action
`A curvearrowright A/H` is sofic. By
[[gkp-sofic-action-is-liftable-hamming-chart-family]], its missing datum is
a positive-density common-carrier family of liftable Hamming charts; one
selected coefficient supplies no such family.
