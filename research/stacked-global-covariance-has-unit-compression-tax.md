---
rg: 2
id: stacked-global-covariance-has-unit-compression-tax
kind: claim
title: Stacking globally covariant context rows preserves the full source-commutator tax
distinct_from:
  global-covariance-misses-capacity-compression: that exhibits the uncontrolled commutator for one row; this proves an exact square-function identity for arbitrarily many rows and shows that averaging, orthogonal stacking, or expander repetition cannot reduce its coefficient below one.
  capacity-gated-common-corner-bcs-two-cell: that proves a genuinely compressed common-source row controls the localized BCS functional; this rules out manufacturing that row by stacking uncompressed global covariance relations.
---

Let `Z` be a unitary, let `Q` be a projection, and for `1<=c<=N` let
`v_c,a_c` be unitaries.  Put

```text
g_c=a_c v_c-v_c Z,                                      (SCT1)
d_c=a_c v_c Q-v_c Q Z.                                  (SCT2)
```

Then

```text
d_c=g_c Q+v_c[Z,Q].                                     (SCT3)
```

In particular, if every global covariance is exact, `g_c=0`, then

```text
sum_c ||d_c||_2^2=N||[Z,Q]||_2^2.                       (SCT4)
```

The same tax survives normalized orthogonal stacking.  On the Hilbert-space
direct sum of the `N` target copies define

```text
S=N^(-1/2)(v_1Q,...,v_NQ)^T,
A=diag(a_1,...,a_N).                                    (SCT5)
```

Then `S^*S=Q`; and if `a_cv_c=v_cZ` for all `c`,

```text
||AS-SZ||_2^2=||[Z,Q]||_2^2.                            (SCT6)
```

Thus repetition does not average the compression error down: unnormalized
stacking multiplies both sides by `N`, while normalized stacking leaves the
coefficient exactly one.

Quantitatively, for arbitrary global defects, the Hilbert direct-sum triangle
inequality gives

```text
(sum_c||d_c||_2^2)^(1/2)
 >=sqrt(N)||[Z,Q]||_2-(sum_c||g_c||_2^2)^(1/2),         (SCT7)
```

and the reverse inequality with `+` also holds.  Hence no number of global
conjugacy/covariance relators, no orthogonal row packing, and no regular
expander weighting can absorb the `Q`-commutator with a coefficient smaller
than one.  A successful common-source cell must wordize a genuinely
capacity-gated mixed row, or introduce an additional matrix-only term that
already controls `[Z,Q]`; global covariance plus averaging cannot supply it.

