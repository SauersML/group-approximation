---
rg: 2
id: matrix-homogeneous-ucp-retracts-can-hide-defect
kind: claim
title: Exact matrix-homogeneous covariance does not force a split ucp retract into the multiplicative domain
distinct_from:
  scalar-covariant-odd-even-ucp-retract-is-impossible: that treats the one-dimensional scalar homogeneous line and proves rigidity; this shows arbitrary finite matrix coefficients are already flexible enough to hide positive defect.
  split-ucp-matrix-retracts-can-hide-defect-in-a-boundary-ideal: that is a finite-dimensional state-summand example without group covariance; this constructs coaction-equivariant examples on every twisted group algebra admitting a nontrivial positive-definite multiplier.
  finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres: that concerns matrix coefficients forming an exact projective representation; here the coefficient matrices are only positive-definite compressions and need not be unitary or multiplicative.
---

**ESTABLISHED COVARIANT COUNTERMODEL.**  Let `G` be any discrete group,
`alpha` any circle-valued multiplier, and `f:G->C` a normalized
positive-definite function.  The Fourier multiplier

```text
M_f:C^*(G,alpha)->C^*(G,alpha),       M_f(u_g)=f(g)u_g
```

is ucp.  Hence

```text
i_f(a)=diag(a,M_f(a)),             r([[a,b],[c,d]])=a    (MHR1)
```

are ucp, `r i_f=id`, and `i_f` is a complete-order embedding.  Both maps are
exactly equivariant for the canonical `G`-coaction, and on homogeneous
generators

```text
i_f(u_g)=diag(1,f(g)) tensor u_g.                         (MHR2)
```

If `|f(g)|<1`, the second diagonal block in `(MHR2)` has a nonzero positive
multiplicative defect killed by `r`.  Thus exact canonical grading/coaction
covariance with arbitrary finite matrix coefficients does **not** force
multiplicative-domain behavior.

There is no qualitative rescue from approximate scalar covariance alone.
For `G=Z/2`, the functions `f_t(e)=1`, `f_t(s)=t`, `0<t<1`, are positive
definite.  Then

```text
dist(i_(f_t)(u_s), C(I_2 tensor u_s)) <= 1-t -> 0,
```

while every finite stage still has a nonzero hidden defect.  Approximate
scalar-line covariance does make the defect tend to zero in this example,
but does not make any individual retract multiplicative.  Promoting an
asymptotic covariance estimate to an exact odd-Maslov obstruction therefore
requires an additional quantitative stability/gap theorem; it is not a
formal ucp consequence.

This countermodel uses the same twist on source and target, so it does not
construct the desired odd-to-even Maslov retract.  It sharply separates the
logical levels: scalar-line exact covariance closes the Maslov lane, general
matrix homogeneous covariance does not, and approximate covariance needs a
new modulus.

The twist difference does produce one real restriction not visible here.
`odd-maslov-homogeneous-coefficients-have-a-fixed-size-defect-gap` proves
that an odd-to-even homogeneous map has a uniform positive coefficient
defect at every fixed matrix size.  Hence the present construction is a
formal covariance countermodel, but it does not refute Maslov-specific
scalarization after uniformly bounded coefficient degree has been fixed.
The unbounded-degree version is now fenced as well by
`odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap`: vanishing
coefficient boundary would produce an amenable trace on the odd fibre.  The
present countermodel therefore proves flexibility only when the twist
difference is trivial; it does not model an asymptotically scalar odd/even
bridge.

The proof is `positive-definite-fourier-multiplier-retract-proof`.
