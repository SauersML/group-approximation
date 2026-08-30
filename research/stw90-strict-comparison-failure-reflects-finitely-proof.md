---
rg: 2
id: stw90-strict-comparison-failure-reflects-finitely-proof
kind: route
title: Approximate a robust failed comparison by two group-ring squares
target: stw90-strict-comparison-failure-reflects-finitely
requires: []
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

Put `A=C*_r(G)`.  Failure of strict comparison gives `a,b in (A tensor K)_+`
such that

```text
d_tau(a)<d_tau(b),                 a not <=_Cu b.      (2)
```

There is `epsilon_0>0` for which `(a-epsilon_0)_+ not <=_Cu b`; otherwise
the cutdown characterization of Cuntz comparison would give `a<=_Cu b`.
Also

```text
d_tau(b)=sup_(t>0) d_tau((b-t)_+).
```

Consequently one can choose a positive rational `r` so small that

```text
4r<epsilon_0,
d_tau(a)<d_tau((b-2r)_+).                            (3)
```

Matrices over `C[G]` are dense in `A tensor K`.  Approximate `a^(1/2)` and
`b^(1/2)` by finite matrices `z,w` over `C[G]`, enlarging to one common
matrix size, so that

```text
x=z* z,        y=w* w,
norm(a-x)<r,   norm(b-y)<r.                           (4)
```

The standard perturbation lemma

```text
norm(c-d)<eta  =>  (c-(t+eta))_+ <=_Cu (d-t)_+
```

applied in both directions to (4) gives

```text
(a-4r)_+ <=_Cu (x-3r)_+ <=_Cu (a-2r)_+,
(b-2r)_+ <=_Cu (y-r)_+  <=_Cu b.                     (5)
```

Write `X=(x-3r)_+` and `Y=(y-r)_+`.  From (3)--(5),

```text
d_tau(X) <= d_tau(a)
         < d_tau((b-2r)_+)
         <= d_tau(Y).                                (6)
```

Moreover `(a-4r)_+ not <=_Cu b`: since `4r<epsilon_0`, comparison of the
larger cutdown `(a-4r)_+` with `b` would imply comparison of
`(a-epsilon_0)_+` with `b`.  If `X<=_Cu Y`, (5) would therefore give the
contradiction

```text
(a-4r)_+ <=_Cu X <=_Cu Y <=_Cu b.
```

This proves (1).

Only finitely many group elements occur in the entries of `z,w`.  Let `H`
be the subgroup they generate.  Reduced-norm injectivity embeds
`C*_r(H)` into `C*_r(G)`, and the canonical traces agree on this subalgebra.
Thus the dimension inequalities in (6) are the same when calculated in
`C*_r(H)`.  If `X<=_Cu Y` held in `C*_r(H)`, it would hold after the
inclusion into `C*_r(G)`, contrary to the preceding paragraph.  Hence the
same certificate proves failure in the finitely generated subgroup.

**Trust boundary.**  The proof uses only density of the group ring, reduced
subgroup inclusions, the cutdown characterization of Cuntz comparison, lower
semicontinuity of the dimension function through cutdowns, and the displayed
quantitative perturbation lemma.  No selflessness or directed-union theorem
is used.  Simplicity does not pass to the support subgroup, so no stronger
reduction is asserted.
