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

Every finite-stage block group is nilpotent. The question is whether depth
survives into a simple limit without bound. The opposite answer would be a
theorem: the component group of every simple unital C*-algebra, or of every
simple AH algebra, is nilpotent, perhaps of universally bounded class. Known
simple examples reach class at least four (simple-cstar-unitary-components-class-four,
unreviewed). Class five is open (simple-cstar-unitary-components-class-five).

## Attempts

- *Unital AH limits.* Constrained, not dead. By
  block-component-group-class-at-most-excess-plus-two the group is locally
  nilpotent, and depth c needs blocks of excess at least c − 2 cofinally. By
  ah-unitary-component-kernel-is-locally-finite every commutator has finite
  order, finitely generated subgroups are center-by-finite, and each
  commutator dies in some M_n(A). A non-nilpotent example must therefore
  carry finite p-groups of unbounded class, for one prime or across primes.
- *Seed witnesses in a protected block of fixed rank k.* Dead for bounded k.
  A witness (f o pr_M) (+) 1_Q with f a nested commutator of maps M -> U(k)
  is null once the depth reaches the Berstein–Ganea nilpotency of U(k). That
  number is finite: Costoya–Scherer–Viruel, arXiv:1504.06100v2, p. 2, write
  "Work of Hopkins, [24], and Rao, [40], gives a complete understanding of the
  classical Berstein–Ganea nilpotency for compact Lie groups: those with
  finite nilpotency index are precisely the torsion free ones". U(k) is
  torsion free. For k = 2 every homology-theory detector already stops at
  depth three (rank-two-trapping-blind-to-depth-four-brackets). A seed-based
  example needs protected ranks k_c -> ∞, for instance one summand of the
  inductive system per depth.
- *Trapping detectors see only the stable commutator.* Every trapped
  invariant of a seed witness is a homology class of the seed, so it depends
  only on Sigma^∞ of the nested commutator map (proof as in
  rank-two-trapping-depth-four-stable-null-proof, Detection). What matters is
  whether the stable depth of U(k) grows with k. Two heuristics, neither
  proved. (i) In the metastable range, d up to about 4r, bracketing with a
  seed g should act on the K_1-kernel as module multiplication by
  J(g) − 1. Words are then products of image-of-J stems. At odd primes these
  square to zero, and the depth stays small. (ii) Beyond that range the
  letters are general self-maps of Sigma^∞ SU(k), not multiplications by
  stems. An example is a map dropping p − 2 cells through alpha_1.
  Composites of such maps can be Toda brackets, such as
  beta_1 in <alpha_1, ..., alpha_1>, and those have long nonzero powers.
  Growth of the depth, if it happens, must come from (ii). Trapping towers
  sit near the boundary, dim Y_i ≈ 4·rank. Detecting beta_1 would need a
  structure on TX − W_R that trivializes the p-local J-image in a range,
  which is finer than Spin or lambda mod 8.
- *Wedge or direct sum of trapping towers.* Plan. One inductive system can
  carry several trapping summands: different seeds, protected ranks and
  tangential structures, with evaluation blocks mixing the summands for
  simplicity. The mixing must preserve each summand's Euler number. This is
  not yet written down. It becomes useful once seeds of unbounded depth
  exist.
- *Non-AH constructions.* Crossed products, reduced group C*-algebras and
  Cuntz–Pimsner algebras that are simple usually have stable rank one, are
  Z-stable, or are purely infinite. Each forces K_1-injectivity, so the
  component group is abelian. No non-AH simple C*-algebra with a nonabelian
  component group is known to this lane. The check was bounded to the repo
  graph and Toms arXiv:2609.09535v1.
