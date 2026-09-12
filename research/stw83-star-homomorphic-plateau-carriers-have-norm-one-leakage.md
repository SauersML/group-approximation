---
rg: 2
id: stw83-star-homomorphic-plateau-carriers-have-norm-one-leakage
kind: claim
title: Star-homomorphic moving plateau carriers necessarily leak a positive coefficient cutoff
distinct_from:
  stw83-compressed-one-colour-carries-circle-matrix-finite-sets: that proves arbitrary finite-set accuracy after compression; this quantifies why its uncompressed star-homomorphic return cannot approximate a plateau-supported positive coefficient.
  stw83-circle-unitary-order-zero-plus-constants-gap: that is an abelian winding obstruction on a unitary input; this is a noncommutative constant-spectrum obstruction on a positive input and locates the unavoidable complementary-corner leakage.
---

**ESTABLISHED.**  Let `F` be finite dimensional, let

```text
pi:F->M_r(C(T))
```

be a unital star homomorphism, let `b in F` be a positive contraction, and
let `0<p<1` be a constant projection with `q=1-p`.  Suppose
`f in C(T)` is a positive contraction with

```text
f(t_+)=1,                 f(t_-)=0.
```

If `0<epsilon<1/2` and

```text
norm(p pi(b) p-fp)<epsilon,                              (1)
```

then the off-plateau leakage at the zero of `f` satisfies

```text
norm(q pi(b)(t_-) q)
 >=(sqrt(1-epsilon)-sqrt(epsilon))^2.                   (2)
```

In particular, the lower bound in (2) tends to one as the compressed
approximation error tends to zero.

Applied to
[[stw83-compressed-one-colour-carries-circle-matrix-finite-sets]], this
shows that the moving star-homomorphic frame solves simultaneous compressed
coefficient encoding only by moving an almost norm-one positive block into
the complementary corner wherever the target coefficient cutoff vanishes.
That leakage cannot be discarded or cancelled by another completely
positive colour.

Therefore a dimension-one proof for the canonical `A_N` cannot use a
star-homomorphic moving frame alone.  It must taper a genuinely nonunital
order-zero support so that the leakage is extinguished inside the scalar
buffer, while still coordinating that support with the other colour and the
Toeplitz shift.  This is an obstruction to this precise implementation, not
a nuclear-dimension-two lower bound.

DERIVATION
[[stw83-star-homomorphic-carrier-leakage-proof]]
