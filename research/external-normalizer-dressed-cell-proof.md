---
rg: 2
id: external-normalizer-dressed-cell-proof
kind: route
title: Classify signed-normalizer centralizers of the concrete depth-two cell
target: external-normalizer-dressed-cell-has-full-gauged-gram
requires:
  - mixed-whitehead-cell-moves-signed-source
  - eight-external-returns-have-no-whitehead-gauge-lock
---

Use root positions `x_ab=1+E_ab`.  The depth-two cell uses

```text
g_*=x_28(1)x_49(1),       Y_2=x_83(b_2),
A_(2,2)=x_12(a_2).                                     (1)
```

The root `x_59(1)` has disjoint Steinberg indices from every factor in
`(1)`, proving `(SCT2)`.  Since it is an involution, direct inversion of
`H'=Hn` gives `(SCT3)`.  Conjugating `(1)` proves that `H,H'` have identical
cell images.

For completeness, test all eight external normalizing roots against the
four elementary factors in `(1)`.  Every root except `x_59(1)` shares a
source-target incidence with at least one factor.  Closing the test over all
`21` signed-normalizing constant roots leaves seven internal roots and this
one external root.  This is the complete shortest root-dressing table.

Now `nQ=Qn` because `n` normalizes the signed pair.  Also
`Q'=HQH=HnQnH`, so the identities `(SCT4)--(SCT5)` follow by direct
multiplication and `H^2=n^2=1`.  The external signed-normalizer theorem gives
the factorization `(SCT6)` and its arbitrary multiplicity involution.
Internal `L_0` dressings act by `lambda_0` on `Q` and hence only contribute
a scalar.  This proves the claimed exhaustive short-dressing and full-Gram
fence.

For the odd-anchor cross-check, use factor tuples in the repository's
`(source,target,coefficient)` convention.  Therefore

```text
J_2=whitehead(8,9,2),
```

not `whitehead(9,8,2)`.  Sparse Leavitt matrix multiplication then verifies
`M^7=C^5=1`.  Direct root incidence already proves that `n` commutes with
`W,A_2`; multiplying the four remaining commutators proves `(SCT9)`.
Comparison with the five powers of `C` shows that `nCn` is none of them,
and the five exact conjugates `C^k n C^(-k)` are distinct.

Finally enumerate the `8192` constant matrices of `L_0`, conjugate each by
`M` and by `C`, and compare faithful Leavitt normal forms.  In each case only
the identity returns to `L_0`, proving `(SCT10)`.  Since a compression
`Q U Q` is a fixed-source operator only when `U` returns the signed source,
`M` and `C` cannot turn their odd-order relations into an equation for
`n|Q=N_59 tensor E_59`.  Multiplying the five conjugates in cyclic order
gives a nonidentity word as well.  This proves the odd-anchor extension of
the fence.
