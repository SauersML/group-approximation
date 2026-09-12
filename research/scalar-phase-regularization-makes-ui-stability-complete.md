---
rg: 2
id: scalar-phase-regularization-makes-ui-stability-complete
kind: claim
title: Scalar phases make uniformly integrable input stability a complete test class
artifacts:
  - research/artifacts/parallel-ui-iteration-audit-2026-09-04.md
---

Let `P=<S|R>` be a finite group presentation. All Schatten norms use
normalized trace. For a tuple `U_j:S->U(d_j)`, write

```text
delta_j=max_(r in R)||U_j(r)-I||_2.
```

A positive-defect sequence has uniformly integrable normalized residuals
if, writing `A_(j,r)=(U_j(r)-I)/delta_j`,

```text
lim_(M->infinity) limsup_j max_r
 ||A_(j,r) 1_(|A_(j,r)|>M)||_2=0.                       (SPR1)
```

Suppose some defining relator has a nonzero exponent-sum vector. Every
sequence with `delta_j->0` is then at generatorwise normalized-HS
distance `o(1)` from another sequence `W_j` in the same dimensions whose
positive defining defects tend to zero and satisfy `(SPR1)`. In fact its
normalized relator residuals converge in 2-norm to scalar matrices.

Consequently, qualitative HS stability restricted to inputs satisfying
`(SPR1)` is equivalent to unrestricted qualitative HS stability for this
presentation. The equivalence holds both for correction in the original
dimensions and for flexible correction with relative dimension change
tending to zero. Finite-abelianization groups with a nonempty generator
set satisfy the exponent-sum hypothesis.

There is also a version without any exponent-sum hypothesis. Adjoin a
generator with its defining triviality relation:

```text
P^+=<S,z | R,z=1>.
```

Uniformly integrable input stability for `P^+` is equivalent to
unrestricted stability for `P`, in either dimension convention. In the
forward direction take `W_j(s)=U_j(s)` and
`W_j(z)=exp(i t_j)I`, where `t_j->0` and `delta_j/t_j->0`. The old
normalized residuals tend to zero and the `z` residual tends to `iI`.

Thus a one-step improvement of uniformly integrable defects, even one
preserving their normalized profile, does not by itself prove stability
on a weaker qualitative input class. Exactness after infinite correction
remains a separate requirement. This claim does not establish stability
or nonhyperlinearity.

DERIVATION
scalar-phase-ui-completeness-proof
