---
rg: 2
id: stw61-finite-rank-side-maximal-commutator
kind: claim
title: A represented finite-rank projection side forces maximal commutators for every mixed unitary
distinct_from:
  stw61-mf-coefficient-maximal-commutator: This uses an infinite-dimensional representation with one finite-rank projection side, including the non-MF classical Toeplitz algebra, rather than matrix-quotient coefficient approximations.
  stw61-circle-properly-infinite-coefficient-maximal-commutator: This permits the distinguished projection and the entire one-isometry coefficient algebra; its moving threshold removes the fixed-commutant restriction but requires a represented finite-rank side.
artifacts:
  - research/artifacts/stw61-finite-rank-side-threshold-obstruction-2026-09-05.md
---

Let D be a unital C*-algebra and p a projection. Suppose a unital
representation rho:D -> B(H), with H infinite-dimensional and
separable, sends p or 1-p to a nonzero finite-rank projection.
Then in the full unital free product C=C(S1)*D,

```text
||[z,WpW*]||=1   for every W in U(C).
```

The representation need not be faithful, and W is unrestricted.

In particular, every nontrivial projection of the classical
Toeplitz algebra satisfies this theorem for all mixed unitaries
over that whole coefficient algebra. Isometric free-product
inclusion gives ||[z,W(s1s1*)W*]||=1 for every W in U(C*(z,s1))
inside C(S1)*T2, including arbitrary uses of s1, its range
projection, and unitary functional calculus.

For the defect e=1-s1s1*-s2s2* of T2, the theorem gives
||[z,W e W*]||=1 for every W in the entire U(C(S1)*T2).
The defect is nonfull, so this unrestricted result does not
supply the properly infinite full projection pair required
by the BRR criterion.

No unital representation of T2 can make either side of
p=s1s1* finite rank. The simultaneous two-isometry case
for that projection remains outside the theorem, and LXI
remains open.

ROUTES

stw61-moving-threshold-compression-proof
