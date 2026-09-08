---
rg: 2
id: leavitt-first-relation-has-a-4608-dimensional-seed
kind: claim
title: Projective incidence gives an exact first-relation seed in dimension 4608
distinct_from:
  leavitt-24k-first-relation-has-exact-finite-model: that uses the 115379712-dimensional finite-group regular representation; this supplies a 4608-dimensional model from explicit projective permutation spaces and verifies its failure on two further coefficient relators.
  binary-leavitt-hyperlinear-iff-24k-feasible: that characterizes the entire relation exhaustion uniformly over dimensions; this supplies one finite exact seed at k=192 and does not model the full Leavitt unit group.
artifacts:
  - research/artifacts/leavitt-4608-projective-incidence-seed-2026-09-08.md
---

Let `F_8=F_2[alpha]/(alpha^3+alpha+1)`, and in `SL_3(F_8)` take

```text
c=(123),
b_1=x_12(alpha), b_2=x_12(alpha^(-1)), b_3=x_12(1).
```

Let `V` be the 72-dimensional augmentation subspace of the complex
permutation space on the 73 projective points. Let `J` be the
512-dimensional cycle space of the point-line incidence graph, with
73 point vertices, 73 line vertices, and 657 edges. Then the explicit
unitary representation

```text
W=Lambda^2(V) direct-sum 4(J direct-sum 1)
```

has dimension `4608=24*192`. Its restrictions are exactly

```text
W|_<c> = 1536 copies of the regular C_3 representation,
W|_<b_1,b_2,b_3> = 576 copies of the regular C_2^3 representation.
```

Consequently it gives a frozen relative-unitary model at `k=192`
with `pi(r_*)=I`, for the first relation of
`leavitt-24k-first-relation-has-exact-finite-model`. The construction
uses only explicit point, line, flag, and exterior-power actions;
no finite-group regular enumeration is needed. A simpler optional
model `V direct-sum 2 Lambda^2(V)` has dimension `5184=24*216`
and the same regular-restriction property.

This seed does not satisfy the full coefficient relations. With
`gamma=Ad(c)` and words

```text
d=[b_2,gamma(b_1)], h=gamma^2(d), a=[d,h],
u=[b_2,gamma(b_3)], w=[gamma^2(b_1),a],
R_0=[u,w],
R_sum=[[b_1,gamma(b_2)],h]
      [[b_3,gamma(b_1)],gamma^2(u)] a^(-1),
```

both `R_0` and `R_sum` evaluate to `x_12(1)`. Their images in
either seed have normalized trace zero and HS distance exactly
`sqrt(2)` from the identity. No optimal dimension, vanishing of
all relation defects, hyperlinearity, or nonhyperlinearity is asserted.
