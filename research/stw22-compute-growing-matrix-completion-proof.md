---
rg: 2
id: stw22-compute-growing-matrix-completion-proof
kind: route
title: Complete the changing matrix field and replicate its shrinking cuts
target: stw22-matrix-to-hyperfinite-field-trace-continuity
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-matrix-to-hyperfinite-field-audit-2026-08-30.md
---

Put `X={infinity,1,2,...}`.  Coordinatewise scalar multiplication makes
`A` a unital `C(X)`-algebra.  Evaluation gives the unique-trace fibres
`F_n` at `n` and `U` at infinity.  Equivalently,

```text
0 -> direct-sum_n^c0 F_n -> A -> U -> 0.
```

This proves separability and nuclearity.  Disintegration over the central
copy of `C(X)`, followed by uniqueness of the trace on every fibre, gives

```text
T(A)=Prob(X).
```

Hence the uniform tracial norm is the supremum of the coordinate `2`-norms.

We next verify the displayed description of `M`.  Uniform `2`-norm limits
of bounded elements of `A` plainly have the stated coordinates and
`2`-convergence at infinity.  Conversely, let `a` satisfy that description
and fix `epsilon>0`.  Approximate `a_infinity` in `2`-norm by a bounded
element `u in U`.  After changing finitely many coordinates exactly, it is
enough to treat the tail.  Since the increasing union of the `F_n` is norm
dense in `U`, choose bounded `u_n in F_n` with

```text
||u_n-u|| -> 0.
```

The section with limit coordinate `u`, the prescribed finitely many
coordinates, and tail `(u_n)` belongs to `A`; on a sufficiently late tail
it is uniformly `2`-close to `a` because both `a_n` and `u_n` are
`2`-close to `a_infinity`.  This proves the completion formula.

At an isolated point `n`, a central scalar function which is zero at `n`
and one elsewhere shows `J_n=K_n`.  At infinity, evaluation and central
truncation give

```text
K_infinity={a in M:a_infinity=0},
J_infinity={a in K_infinity:||a_n|| -> 0}.
```

Thus the only possible gap is

```text
I={[(a_n)]: ||a_n||_2 -> 0}
  triangleleft (product_n F_n)/(direct-sum_n^c0 F_n).       (GMG)
```

Let `sigma` be a bounded positive trace on `I` and let
`a=[(a_n)]` be a positive contraction.  For `epsilon>0`, set

```text
b_n=(a_n-epsilon)_+,       p_n=1_(epsilon,infinity)(a_n).
```

Then

```text
tr_(F_n)(p_n) <= epsilon^(-2)||a_n||_2^2 -> 0.
```

Write `F_n=M_(k_n)`.  Fix `m`.  Cofinitely,
`m rank(p_n)<=k_n`, so in the matrix factor `F_n` the projection `p_n` has
`m` pairwise orthogonal unitarily equivalent
copies.  Coordinatewise conjugation therefore produces, modulo the `c_0`
sum, `m` orthogonal conjugates of `b`.  The canonical multiplier extension
of `sigma` is tracial, and hence

```text
m sigma(b) <= ||sigma||.
```

Since `m` is arbitrary, `sigma(b)=0`.  As `||a-b||<=epsilon`, letting
`epsilon` decrease to zero gives `sigma(a)=0`; hence `sigma=0`.

Finally, density in the infinite-dimensional `UHF` algebra forces
`k_n -> infinity`.  Rank-one projections `q_n in F_n`
satisfy `||q_n||=1` and `||q_n||_2=k_n^(-1/2)->0`, so their class is a
nonzero element of `(GMG)`.  The gap is therefore nonzero but bounded-
trace-free.  Applying
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` proves that every
trace on `M` is the integral of the canonical fibre traces.
