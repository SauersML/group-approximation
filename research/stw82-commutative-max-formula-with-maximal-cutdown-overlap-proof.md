---
rg: 2
id: stw82-commutative-max-formula-with-maximal-cutdown-overlap-proof
kind: route
title: Prove maximal overlap in the interval endpoint extension
target: stw82-commutative-max-formula-with-maximal-cutdown-overlap
requires:
  - stw82-order-zero-direct-sum-support-criterion
  - stw82-complementary-cutdowns-merge-iff-near-projections
---

The ideal in (E1) consists exactly of the continuous functions vanishing at
both endpoints.  Choose `f in C_0((0,1))_+` and `t_0 in (0,1)` with
`f(t_0)=1`.  Since `(h_lambda)` is an approximate unit,
`h_lambda(t_0)f(t_0) -> f(t_0)`, so eventually
`h_lambda(t_0)>1/2`.  But `h_lambda(0)=0`.  The intermediate value theorem
then supplies `s_lambda in (0,t_0)` with `h_lambda(s_lambda)=1/2`.  Since
`0<=t(1-t)<=1/4` on `[0,1]`, this proves (E2).  Quasicentrality is automatic
because the ambient algebra is commutative.

For locally compact metrizable spaces, the nuclear dimension of the
commutative algebra is its covering dimension.  Thus the ideal and middle
algebra in (E1) have nuclear dimension one, while the two-dimensional
quotient has nuclear dimension zero, proving (E3).  Finally, the two raw
support images have product `h_lambda(1-h_lambda)`.  The direct-sum support
criterion shows that this is precisely the cross-colour obstruction, and
the quantitative complementary-cutdown claim shows that no vanishing-norm
orthogonal perturbation of these supports exists.
