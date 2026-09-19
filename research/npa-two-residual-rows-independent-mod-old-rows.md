---
rg: 2
id: npa-two-residual-rows-independent-mod-old-rows
kind: claim
title: The two old-class rows of a new level survive modulo the previous level
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

For `k >= 4` the two level-`k` rows

```text
A_k = < T_[((0),r_(k-2))] , Gamma_k(y) T_[((0),r_(k-1))] >,
B_k = < D_[(empty,e_(k-3))] , Gamma_k(y) D_[(empty,e_(k-2))] >,
```

both supported entirely on moment classes of degree at most `2k-2`, are linearly
independent modulo the row space of `Phi_(k-1)`.

The mechanism is a projection onto the three level-`(k-1)` unseen coordinates
`(empty,m)`, `((0),m)`, `((1),m)` with `m = r_(2k-3)`:

```text
A_k |_(U_1,U_3,U_4) = ( 2, -2,  0),
B_k |_(U_1,U_3,U_4) = ( 2,  0, -2),
```

which are independent.  So the claim follows the moment one knows that every row
of `Phi_(k-1)` projects to zero there -- and that, not the projections, is the
content.

`A_k` is in closed form and proved: see
`npa-first-residual-gauge-row-closed-form`.  The `B_k` six-term dressing identity
is asserted by the ingesting dossier; only its `(empty,m) - ((1),m)` signature,
which matches the imported germ step's second residual condition, was checked
here.

## Attempts

The route `npa-residual-rows-independent-via-unseen-freeness` is the only attack
on record, and it reduces the claim to the freeness of the unseen coordinates at
level `k-1` plus the two explicit row identities.  That reduction is sound and
short; it simply moves the whole difficulty into the freeness lemma.

An attack that avoids freeness, not tried: show directly that `A_k` and `B_k` are
not in the span of `row Phi_(k-1)` by pairing them against two explicit vectors of
`ker Phi_(k-1)`.  A row of `Phi_(k-1)` annihilates every kernel vector, so
exhibiting `z_1, z_2` in `ker Phi_(k-1)` with the matrix `[A_k . z_i ; B_k . z_i]`
nonsingular settles it without any statement about supports.  This looks strictly
easier than proving freeness, because it needs two kernel vectors rather than a
statement about all rows, and the face family `y_0(delta)` is a supply of kernel
vectors that the imported kernel law already certifies.
