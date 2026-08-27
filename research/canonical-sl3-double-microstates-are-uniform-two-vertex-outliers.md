---
rg: 2
id: canonical-sl3-double-microstates-are-uniform-two-vertex-outliers
kind: claim
title: Every sufficiently canonical SL3 double microstate has two uniformly uncorrectable vertices
distinct_from:
  sofic-sl3-vertex-action-produces-two-outlier-double-models: that conditionally constructs permutation microstates from a sofic building action; this proves the two-outlier conclusion for every canonical double microstate, conditional only on such a microstate existing.
  sl3-canonical-double-has-a-correctable-vertex: that asks for one correctable vertex; this proves that every actual canonical sequence has the opposite property and hence that the requested statement can hold only vacuously.
  sl3-double-quasiregular-tensor-is-a-uniform-outlier: that proves the diagonal tensor assignment is uncorrectable; this proves each of the two original vertex assignments is uncorrectable.
---

Put

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),       D=A *_C A,
w=i_0(h)i_1(h)^(-1),       h=diag(2,1,1/2).
```

Fix the presentations and generating sets used by the arithmetic-double
claims.  There are constants `epsilon_0,delta_0,tau_0>0`, independent of
matrix dimension, such that if `sigma` is a unitary assignment for `D` with
presentation defect at most `delta_0` and

```text
|tr(sigma(w))| <= tau_0,
```

then, for both vertex restrictions `pi_j`,

```text
inf_(alpha:A->U(d) exact)
  max_(s in S_A)||pi_j(s)-alpha(s)||_2 >= epsilon_0,
  j=0,1.                                                   (CTO1)
```

In particular every canonical-character microstate sequence of `D`, if one
exists, eventually has **both** vertices uniformly far from every exact
finite-dimensional representation of `A`.

The point is the contrapositive of the completed anchor-and-fold package.
If one vertex were closer than `epsilon_0` to an exact representation, the
dimension-free modulus in
`sl3-double-one-near-vertex-forces-joint-near-exactness` would correct the
other vertex to the same representation.  The dimension-free modulus in
`sl3-arithmetic-double-near-exact-vertices-fold-projectively` would then
force `|tr(sigma(w))|` arbitrarily close to `1`.  Choosing the fixed defect
and correction thresholds so that this lower bound exceeds, say, `3/4`, and
then taking `tau_0=1/4`, gives `(CTO1)`.

Consequently `sl3-canonical-double-has-a-correctable-vertex` is not an
intermediate stability theorem available on a hypothetical hyperlinear
model.  If `D` is hyperlinear, a canonical sequence exists and `(CTO1)`
refutes that claim.  If `D` is non-hyperlinear, no canonical sequence exists
and the claim is true vacuously.  Thus the correctable-vertex statement is
equivalent, at existence level, to non-hyperlinearity of this fixed double.

This does not decide which side holds.  It does rigorously rule out searching
for a correctable vertex *inside* an extant canonical microstate: any proof
phrased that way must actually exclude the microstate before the correction
is produced.
