---
rg: 2
id: simple-cstar-unitary-component-group-not-nilpotent
kind: claim
title: Some simple unital C*-algebra has a unitary component group U(A)/U0(A) that is not nilpotent
distinct_from:
  simple-cstar-unitary-components-class-four: That asks for one nonzero fourfold commutator; this asks for nonzero c-fold commutators for every c in one algebra.
  ah-unitary-component-kernel-is-locally-finite: That constrains AH component groups; this asks for an example beyond every finite class.
---

**OPEN.** Find a simple unital C*-algebra A such that for every c there are
unitaries u_1, ..., u_c, v in A with [u_c, [..., [u_1, v]...]] not in U_0(A).

Every finite-stage block group is nilpotent, so the question is whether
depth survives into a simple limit without bound. The opposite answer would
be a theorem that the component group of every simple unital C*-algebra
(or every simple AH algebra) is nilpotent, perhaps of class bounded by a
universal constant.

## Attempts

- *Unital AH limits.* Constrained, not dead. By
  block-component-group-class-at-most-excess-plus-two the group is locally
  nilpotent, and depth c needs blocks of excess at least c − 2 cofinally. By
  ah-unitary-component-kernel-is-locally-finite every commutator has finite
  order, finitely generated subgroups are center-by-finite, and each
  commutator dies in some M_n(A). A non-nilpotent example must therefore
  carry finite p-groups of unbounded class, for one prime or across primes.
- *Wedge or direct sum of trapping towers.* Plan. Toms's trapping tower
  (toms-trapped-spin-bordism-class) protects one block C^2 and reads one
  seed. Running towers for seeds of depth 3, 4, 5, ... as summands of one
  inductive system, with evaluation blocks mixing the summands, would reduce
  the problem to *trappable seeds of every depth*. The mixing must preserve
  the Euler number <c_r(Q)^2, [X]> = 1 of each summand. This is not yet
  written down.
- *Seeds in a protected block of fixed rank k.* Where it dies: a witness
  (f o pr) (+) 1_Q with f a nested commutator of maps M -> U(k) is null once
  the depth exceeds the homotopy nilpotency of U(k). Homotopy nilpotency is
  finite for torsion-free finite H-spaces such as SU(k) (recalled from
  Hopkins and Porter; not verified from the sources in this lane). So the
  protected rank has to grow with the depth. Rank-two seeds stop at depth
  four for alpha-brackets (u2-quadruple-samelson-class-four-stage).
- *Metastable brackets, d <= ~4r.* Heuristic only. There N(E) is close to
  stable cohomotopy of X with coefficients in a stunted CP^∞, and bracketing
  with a seed g multiplies by J(g) − 1. At odd primes products of two image-of-J
  elements vanish, which would cap the odd-primary depth at small values.
  Deep examples at p = 2 would need long nonzero products in pi_*^s of
  image-of-J elements. The action formula is not proved here.
- *Non-AH constructions.* Crossed products, reduced group C*-algebras and
  Cuntz–Pimsner algebras that are simple usually have stable rank one, are
  Z-stable, or are purely infinite. Each of these forces K_1-injectivity, so
  the component group is abelian. No non-AH simple C*-algebra with a nonabelian
  component group is known to this lane (check bounded to the repo graph and
  Toms arXiv:2609.09535v1).
