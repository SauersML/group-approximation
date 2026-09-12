---
rg: 2
id: rectangular-hecke-polar-cycle-has-no-strict-trace-gain
kind: claim
title: A closed cycle of bounded-below Hecke compressions has no strict rectangular trace gain
distinct_from:
  closed-multiplicity-cycle-kills-carrier-trace: that charges a closed cycle of algebraic branching cells; this proves before any defect estimate that bounded-below polar arrows around a composable finite-trace cycle must all be onto and equal-trace.
  fixed-rank-index-authenticator-has-gap-or-functoriality: that treats rank and spectral readouts in matrix approximations; this isolates the exact carrier geometry and the separate failure of polar calculus to remain algebraic.
  free-relative-placement-closes-one-balanced-chord: that closes one equal-trace chord after choosing a relative placement; this proves strict rectangular target excess cannot force or canonicalize the resulting balanced holonomy.
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let
`p_0,...,p_(m-1)` be projections with cyclic indices, and let

```text
T_i in p_(i+1) M p_i,
T_i^* T_i >= c_i p_i,             c_i>0.              (RHP1)
```

Write `T_i=v_i |T_i|`.  Then

```text
v_i^*v_i=p_i,       v_i v_i^*<=p_(i+1).               (RHP2)
```

Consequently

```text
tau(p_i)<=tau(p_(i+1))                                  (RHP3)
```

at every edge.  Around the closed cycle all inequalities in `(RHP3)` are
equalities, and faithfulness of `tau` forces

```text
v_i v_i^*=p_(i+1)                                      (RHP4)
```

for every `i`.  Thus every effective polar arrow in a closed composable
cycle is a unitary equivalence between equal-trace carriers.  A compression
into a larger projection can be bounded below, but its polar range is only
an equal-trace subprojection; the target excess is spectator mass.  Feeding
that range into the next edge reduces the alleged rectangular cycle to the
ordinary balanced multiplicity-holonomy problem.

There is also an independent algebraic firewall.  Even when a group-ring
coefficient is uniformly bounded below in the regular von Neumann algebra,
its polar unitary need not belong to the group algebra.  For `G=Z`, with
canonical unitary `u`, the element

```text
T=2+u in C[Z]
```

is invertible in `L(Z)`, but

```text
polar(T)(z)=(2+z)/|2+z|                                (RHP5)
```

is not a Laurent polynomial.  Hence analytic polar transport does not by
itself produce coefficients in a finite-subgroup Hecke corner
`q C[G] q`, and cannot by itself supply the algebraic corner homomorphism
needed for canonical-trace promotion.

This does not rule out a construction with an additional algebraic inverse
or an independently forced equal-trace holonomy relation.  It rules out
strict rectangular rank excess as the mechanism which makes a closed polar
holonomy trivial while retaining a nontrivial ambient label word.
