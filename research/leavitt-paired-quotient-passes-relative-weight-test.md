---
rg: 2
id: leavitt-paired-quotient-passes-relative-weight-test
kind: claim
title: The paired length-six Leavitt quotient passes the relative weight test and preserves both coefficient copies
distinct_from:
  leavitt-paired-relative-picture-local-census: That finite census locates the two torsion folds; this folds them into a global weight argument valid for pictures of arbitrary size.
  leavitt-length-six-full-support-torsion-candidate: That constructs the first candidate surviving the generic small-length theorems; this proves that the candidate nevertheless cannot violate Kervaire-Laudenbach.
artifacts:
  - research/leavitt-paired-quotient-passes-relative-weight-test-proof.md
---

For the paired relative presentation

```text
Q=<H,z | R_0,R_1>,                 H=G_0*G_1,
R_0=h_0 z h_1 z h_2 z^(-1),
R_1=k_0 z k_1 z k_2 z^(-1),
```

with `h_i, k_i` the SPECIFIC labels of
`leavitt-paired-relative-picture-local-census` --
`h_0 = a_0 b_1`, `h_1 = c_0 d_1`, `h_2 = e_0`, `k_0 = a_1`, `k_1 = b_0 c_1`,
`k_2 = d_0 e_1`, so that `h_2` and `k_0` are involutions and the four
zero-weight labels are `u_(i,0) v_(i,1)` with `(u_i) = (a, c, b, d)`
pairwise distinct in `G_0` and `(v_i) = (b, d, c, e)` pairwise distinct in
`G_1` -- the natural homomorphism `H -> Q` is injective.  In particular the
normal closure of `R_0,R_1` has trivial intersection with each `G_i`, so
these two relators do not normally generate the degree-two kernel and the
associated length-six equation is not a Kervaire-Laudenbach counterexample.

**Scope correction (2026-08-22 audit).**  An earlier version stated the
conclusion for ARBITRARY `h_i, k_i`, which is false: with
`h_0 = h_1 = h_2 = 1`, `k_1 = k_2 = 1`, `k_0 = g != 1` in `G_0` one has
`R_0 = z`, `R_1 = g z`, hence `Q = H / <<g>>` and `H -> Q` kills `g`.  The
proof uses exactly the two hypotheses now displayed (involutions at the
weight-one labels, pairwise-distinct junction blocks making every
zero-weight path label of free-product length at least two), and is
correct for the census instance.

