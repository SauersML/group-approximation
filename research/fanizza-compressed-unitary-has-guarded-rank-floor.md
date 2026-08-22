---
rg: 2
id: fanizza-compressed-unitary-has-guarded-rank-floor
kind: claim
title: One compressed ambient unitary has a square-root guarded rank floor
artifacts:
  - research/artifacts/fanizza-one-sided-compressed-rank-floor-2026-08-21.md
distinct_from:
  trace-cyclic-rank-mismatch-checksum: that compares two arbitrary cyclic products and gets a linear trace mismatch; this uses one compressed unitary and obtains the stronger squared-HS rank floor directly.
  universal-block-return-violates-the-regular-firewall: that rules out universal two-product block returns; this identifies the minimal one-product proper-corner residual and its exact finite-dimensional constant.
  support-only-toeplitz-return-cannot-see-heat-decay: that shows support transport cannot read amplitude decay; this authenticates full source Gram against a strictly smaller guarded target.
---

For projections `H<=E` in `M_d(C)`, put `F=E-H`.  For every unitary `U`
and compressed map `X=FUE`,

```text
||X^*X-E||_2^2 >= tr_d(H).                              (OCR7)
```

The proof is rank-nullity: `rank(X)<=rank(F)`, so `X^*X` vanishes on at
least `rank(H)` dimensions of `E C^d`, where `X^*X-E=-I`.

Thus on the canonical guarded D8 packet, where `tr(H)=1/8`, one source-full
compressed return has defect at least `1/sqrt(8)`.  Infinite multiplicity
admits a proper isometry from `E` onto `F`, so the obstruction has exactly
the desired Hilbert-hotel sign.

However, if the compressed partial-isometry equations are fixed
group-algebra identities or follow tracially functorially from relators, the
canonical group trace forces `tau(E)=tau(F)` and kills `H`.  A successful
Fanizza cell must therefore authenticate source fullness through
matrix-coordinate multiplicity selection, not a literal fixed
partial-isometry relation.
