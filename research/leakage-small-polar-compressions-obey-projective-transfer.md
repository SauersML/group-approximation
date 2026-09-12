---
rg: 2
id: leakage-small-polar-compressions-obey-projective-transfer
kind: claim
title: Leakage-small polar compressions obey SL3 projective transfer at arbitrary codimension
distinct_from:
  vanishing-codimension-compressions-obey-projective-transfer: that bounds compression leakage by the deleted rank fraction; this assumes the actual generator leakage is small and removes every codimension restriction.
  projective-trace-square-transfer-for-sl3-pair: that treats arbitrary approximate representations; this only treats polar compressions of exact arithmetic representations and leaves genuinely intrinsic outliers open.
  sl3-noncorrectable-lambda-sector-has-no-projective-leak: that asks to exclude every uniformly noncorrectable canonical lattice microstate; this excludes the subclass admitting an exact ambient dilation with asymptotically invariant compression range.
---

**ESTABLISHED.**  Put `C=SL_3(Z) < A=SL_3(Z[1/2])`, and fix a finite
symmetric presentation-generator packet `S_A` containing `S_C` and `h`.
Let `pi:A->U(H)` be any exact finite-dimensional representation and let `P`
be any nonzero projection of rank `m`, with no restriction on
`m/dim(H)`.  For `s in S_A`, let `rho(s)` be a unitary polar correction of
`P pi(s) P` on `PH`, and set

```text
ell = sum_(s in S_A) ||(1-P)pi(s)P||_HS^2/m.             (LPC1)
```

Then one constant `K`, depending only on the fixed presentation and Kazhdan
data, satisfies for every `U in U(PH)`

```text
1-|tr_PH([U,rho(h)])|^2
 <= K ( sum_(c in S_C)(1-|tr_PH([U,rho(c)])|^2) + ell ). (LPC2)
```

Thus a projective-transfer enemy cannot be obtained by deleting a positive
or even overwhelming fraction of an exact arithmetic representation if the
retained range is asymptotically invariant for the fixed generator packet.
The vanishing-codimension fence is the special case where `ell` is bounded
by the deleted-rank fraction.

This does not cover a polar construction with generator leakage bounded away
from zero whose polar corrections nevertheless satisfy the presentation by
cancellation, nor an approximate representation with no exact ambient
dilation.  Those remain genuine outlier possibilities.

The first exclusion is sharp.  By
`macroscopic-zero-compressions-make-polar-data-universal`, at maximal leakage
every finite unitary tuple is the polar-correction tuple of zero compressions
of one exact finite representation.  Hence the exact-dilation description
has no content without a leakage or singular-overlap hypothesis.
