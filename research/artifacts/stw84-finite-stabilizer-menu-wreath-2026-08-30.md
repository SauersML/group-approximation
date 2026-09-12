---
rg: 2
title: STW LXXXIV checkpoint --- finite menu of arbitrary stabilizers (2026-08-30)
kind: artifact
---

# Result

Let a countable finite-rank abelian group `A` act on `S` with only finitely
many distinct point-stabilizer subgroups, and let `L` be any countable
locally finite lamp group.  If `r=rank_Q(A)>=1`, then

```text
r <= dim_nuc C*((direct_sum_S L) rtimes A)
  <= 2(r+1)9^r-1.
```

For `r=0`, the group is locally finite and the exact dimension is zero.

# Central-field audit

At an Eckhardt--Wu finite-stage fiber `D_x rtimes N`, intersect only the
stabilizer types supporting non-scalar tensor orbits and call the
intersection `J`.  The group `J` fixes every non-scalar coordinate and is
central in `N`; scalar-coordinate permutations are invisible.  Therefore
`D_x rtimes N` is an upper-semicontinuous `C(J_hat)`-algebra.  Amenability
makes the central copy of `C*(J)` injective, and the character fibers are
the scalar-twisted algebras

```text
D_x rtimes_(alpha_bar,omega_chi) N/J.
```

The general separable `C(X)`-algebra nuclear-dimension inequality applies to
this upper-semicontinuous field; no unproved continuity assertion is used.

# Pure-lattice audit

For the finitely many active stabilizers `P_i<=M=N/J`, their intersection is
zero.  In a free finite-index subgroup `M_0<=M`, saturate
`Q_i=M_0 intersection P_i`.  If `d` kills every finite quotient
`bar(Q_i)/Q_i` and `K=dM_0`, then

```text
K intersection P_i=d bar(Q_i).
```

Each right-hand side is pure in `K`.  Hence a nonzero `k in K` lies outside
some `P_i` and has infinite order modulo that `P_i`.  It consequently shifts
an infinite homogeneous orbit of non-scalar tensor factors.  This is exactly
the Bernoulli strong-outerness condition, simultaneously for every nonzero
element of `K`.

If `K` is nonzero, the twisted crossed-product and finite-quotient inputs
give nuclear dimension at most one.  If `K=0`, then `M` is finite; invariant
finite-coordinate crossed products exhaust the fiber and make it AF.  The
case with no active types sets `J=N`, so scalar fibers are correctly charged
to the base `N_hat`.

Thus

```text
dim_nuc(D_x rtimes N)+1<=2(rank(J)+1)<=2(r+1),
```

and the zero-dimensional central spectrum plus the long-thin-cover estimate
costs the factor `9^r`.

# Strict example and scope

For

```text
A=Z^2,
S=A/(Z times 0) disjoint_union A/(0 times Z),
L=Z/2,
```

the two stabilizers are infinite and noncommensurable, with trivial
intersection.  Neither the finite-stabilizer theorem nor the common-
commensurability-core theorem applies, while the new bound is `485`.

This theorem does not subsume the earlier finite-stabilizer result for
actions having infinitely many distinct finite stabilizers; the two results
are complementary.  The remaining permutation-wreath frontier requires an
infinite menu of infinite stabilizer types with no common finite-index core.
