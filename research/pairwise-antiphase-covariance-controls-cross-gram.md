---
rg: 2
id: pairwise-antiphase-covariance-controls-cross-gram
kind: claim
title: Pair-specific opposite phases pay the complete cross-Gram energy
distinct_from:
  disjoint-tag-covariance-controls-cross-gram: that uses pairwise disjoint representations of one fixed finite tag group and an intertwiner spectral gap; this uses a separate target involution for every pair and needs no common tag representation or character packing.
  aggregate-range-idempotence-replaces-gram-bookkeeping: that controls all overlaps from one nonlinear aggregate idempotence defect; this controls each overlap from two linear covariance defects with opposite signs.
---

Let `T_1,...,T_N` be contractions from finite-dimensional source spaces into
one common finite-dimensional target `K`.  For every unordered pair `i<j`,
let `R_ij` be a unitary on `K` and choose signs

```text
epsilon_(i,ij)=-epsilon_(j,ij) in {+1,-1}.
```

Put

```text
D_(i,ij)=R_ij T_i-epsilon_(i,ij)T_i,
D_(j,ij)=R_ij T_j-epsilon_(j,ij)T_j.                 (PAC1)
```

Then

```text
2||T_i^*T_j||_2
 <= ||D_(i,ij)||_2+||D_(j,ij)||_2,                  (PAC2)
```

and consequently

```text
sum_(i!=j)||T_i^*T_j||_2^2
 <= sum_(i<j)(||D_(i,ij)||_2^2+||D_(j,ij)||_2^2).   (PAC3)
```

All norms may be normalized by one common ambient matrix dimension.  If the
`T_i` are partial isometries with final projections `Q_i=T_iT_i^*`, then the
left side of `(PAC3)` is

```text
sum_(i!=j) tau(Q_iQ_j).                              (PAC4)
```

Thus complete pairwise range orthogonality can be paid without packing `N`
disjoint characters into one fixed finite tag group.  The price is a
pair-specific family of covariance comparisons.  This theorem supplies only
the analytic payment.  It does not construct the `R_ij` or prove that the
opposite source phases and all pairwise conjugacy relations extend the exact
non-Connes-embeddable BCS trace.
