---
rg: 2
id: bs14-low-rank-boundary-surgery-preserves-the-regular-face
kind: claim
title: Cutting an exposed BS14 boundary leaves only low-rank cubics but preserves the regular character face
distinct_from:
  even-weil-fixed-line-compression: that performs the surgery on one rank-one arithmetic packet; this proves the block-free rank-r statement and its character consequence.
  bs14-regular-character-forces-sublinear-fixed-source: that proves the source rank is o(d); this computes what cutting such a source does to the involution, inversion, cubics, and trace face.
  bs14-residual-polar-data-build-active-dilation: that must construct a boundary from residual data; this assumes an exact dilation has already exposed its boundary and identifies what remains after cutting it.
---

Let an exact neutral dilation on `QH (+) PH` have `r=dim QH` and

```text
R~=1_Q (+) R,             U~_i=1_Q (+) U_i,
X~=[ C   B* ],            Y~_i=X~U~_i,                (LRS1)
   [ B   A  ]
Y~_i^3=1                 (i=1,2),
```

where `U_1=S^2`, `U_2=RS`.  Put `X_0=sgn(A)`, choosing `+1` on `ker A`.
Then

```text
X_0^2=1,                 X_0 R X_0=R^(-1),            (LRS2)
rank(X_0-A)<=r,
||X_0-A||_F^2 <= Tr(1-A^2)=||B||_F^2<=r.             (LRS3)
```

The kernel convention in `(LRS2)` is valid, not arbitrary.  From
`A^2+BB*=1`, every `v in ker A` satisfies `BB*v=v`; from `B*R=B*`, the
injectivity of `B*` on `ker A` gives `Rv=v`.  Off the kernel,
`AR=R^(-1)A` and commutation of `A^2` with `R` imply the same relation for
the polar sign.

Both remaining cubics have only low-rank error.  There is a universal
constant `C` such that

```text
rank((X_0U_i)^3-1)<=6r,
||(X_0U_i)^3-1||_F<=C sqrt(r)             (i=1,2).    (LRS4)
```

Indeed `P Y~_i^3 P-(P Y~_i P)^3` is a sum of the three length-three paths
which leave `PH`; every term factors through `QH` and has rank at most `r`.
Replacing `A` by `X_0` contributes three telescoping terms, each factoring
through the rank-`r` support of `X_0-A`.  Operator norms are universally
bounded, proving `(LRS4)`.

If `r/d->0`, this surgery changes every fixed group word by `o(1)` in
normalized HS norm.  In particular it preserves all limiting normalized
traces.  Therefore a regular-character dilated sequence remains on the
regular-character face after the boundary is cut and polar-corrected; it
does **not** enter the finite/hyperfinite character sector.

Combining this with
`bs14-regular-character-forces-sublinear-fixed-source` shows that every
already-exposed neutral boundary on the regular face can be removed at
vanishing metric cost, leaving exact involution/inversion and cubic defects
of sublinear physical rank.  This neutralizes the invariant-hull issue for
the **forward** cut: no BS-invariant hull is modified.

It does not solve the reverse problem.  Starting only from two approximate
cubic residuals, their polar carriers need not identify a common boundary:
one carrier mixes source and exit, and general scalar phases make the two
exits nearly parallel.  Thus the remaining tuple is a regular-character
microstate with `o(d)`-rank cubic errors, not a hyperfinite tuple.  Building
the exact `X` still requires the reverse global congruence-atom completion.

