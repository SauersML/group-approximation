---
rg: 2
id: stw81-zero-dimensional-usc-fibre-formula
kind: claim
title: Nuclear dimension of an arbitrary zero-dimensional upper-semicontinuous field is the supremum of its fibre dimensions
distinct_from:
  stw81-zero-dim-simple-fields-obey-trichotomy: that theorem assumes a locally trivial continuous bundle with simple nuclear fibres; the present theorem proves the exact dimension formula for every separable upper-semicontinuous C0-field, with arbitrary fibres and no local triviality.
  stw81-af-fibre-fields-have-base-bound: that theorem allows a finite-dimensional base but requires AF fibres; the present theorem allows arbitrary fibre nuclear dimension and obtains an exact formula when the base is zero-dimensional.
artifacts:
  - research/artifacts/stw81-zero-dimensional-usc-field-audit-2026-08-30.md
---

Let `X` be a second-countable zero-dimensional locally compact Hausdorff
space, and let `A` be a separable `C_0(X)`-algebra.  The field is arbitrary
upper-semicontinuous: no continuity of norm functions, local triviality,
simplicity, or unitality is assumed.  Then

```text
dim_nuc(A)=sup_(x in X) dim_nuc(A_x).                    (ZUF1)
```

The lower bound is fibre quotient monotonicity.  For the upper bound, exact
order-zero lifts of finite-dimensional fibre approximations are localized
on a finite disjoint compact-open partition.  Upper semicontinuity controls
both the approximation error and the norm of the sum of the lifted colours;
a single uniform rescaling makes the assembled return map contractive.

There is a stronger LXXXI consequence when every nonzero fibre is simple.
Then `(ZUF1)` belongs to

```text
{0,1,infinity}.
```

Moreover, for every quotient `D` of `A` and every commutative hereditary
subalgebra `C subset D`, the spectrum of `C` is zero-dimensional.  Indeed a
fibre of `D` is zero or a simple fibre `A_x`.  A non-elementary simple fibre
has no nonzero commutative hereditary subalgebra, while in an elementary
fibre `K(H)` such a subalgebra has rank at most one.  Thus every fibre of
the commutative `C_0(X)`-algebra `C` has dimension at most one as a vector
space.  Its spectrum consequently maps continuously and injectively into
the zero-dimensional space `X`, which forces its spectrum to be
zero-dimensional.

Hence arbitrary upper-semicontinuous zero-dimensional fields with simple
fibres satisfy both the hypothesis and the conclusion of STW Problem
LXXXI, without any bundle charts.
