---
rg: 2
id: torus-knot-group-k34-is-matricially-stable
kind: claim
title: "The (3,4) torus knot group <x,y | x^4 = y^3> is matricially stable: unitaries with A^4 close to B^3 are uniformly close to unitaries with A'^4 = B'^3"
distinct_from:
  matricially-stable-groups-exist: that exhibits some matricially stable groups; this asks for one specific non-virtually-free, non-virtually-abelian one-relator group with infinite centre.
  torus-knot-group-k34-has-central-eigencorners: that is the eigencorner conclusion for K(3,4), which this implies (matricially-stable-groups-have-central-eigencorners); a failure of stability need not produce a corona representation without eigencorners.
  dadarlat-matricial-stability-obstruction: that is the rational-cohomology obstruction; it is silent here because H^2(K(3,4); Q) = 0.
---

**OPEN.**  Let `K = <x, y | x^4 = y^3>`.  Statement: for all sequences
`(A_n, B_n)` in `U(k_n)^2` with `||A_n^4 - B_n^3|| -> 0`, there are
`(A'_n, B'_n)` in `U(k_n)^2` with `A'_n^4 = B'_n^3` and
`||A_n - A'_n|| + ||B_n - B'_n|| -> 0`.

Since `K` is presented by one relator on these generators, this is the same
as matricial stability of `K` in Dadarlat's point-norm sense.  Given an
asymptotic homomorphism `phi_n`, apply the statement to
`(phi_n(x), phi_n(y))`.  The exact pairs define homomorphisms `psi_n`, and
asymptotic multiplicativity gives `||psi_n(g) - phi_n(g)|| -> 0` for every
word `g`.

## Position in the graph

It implies `torus-knot-group-k34-has-central-eigencorners`
(`matricially-stable-groups-have-central-eigencorners`).  Through
`lifted-thompson-t-eigencorners-via-torus-knot-cover`, it therefore implies
`lifted-thompson-t-centre-has-commutant-eigencorners`.  Together with
`thompson-t-has-full-mf-radical` it then implies `lifted-thompson-t-is-not-mf`.
It mentions no Thompson group.

## Evidence

- **The smallest case is stable.**  `K(2,2) = <p, q | p^2 = q^2>` is the
  wallpaper group `pg`.  Eilers-Shulman-Sørensen (arXiv:1808.06793) prove it
  matricially stable.  Verbatim: "Theorem 4.9. BS(1, −1) is matricially
  stable but not weakly C∗-stable. Proof. Since BS(1, −1) is isomorphic to
  the crystallographic group pg = ⟨x,y | xy = y−1x⟩ = ⟨p,q | p2 = q2⟩ ...
  By Corollary 4.2 it is matricially stable."  This holds although `pg`
  contains `Z^2` with index 2, and `Z^2` is not matricially stable.  So
  "contains a non-stable subgroup of finite index" is not an obstruction for
  this family.  This matters because `K(3,4)` contains
  `ker(K -> Z/12) ≅ F_6 × Z` with index 12, and `F_6 × Z` is not
  matricially stable.  That follows from Dadarlat's Theorem 1.1, with
  `H^2(F_6 × Z; Q) = Q^6`.
- **The known obstruction vanishes.**  Dadarlat, Theorem 1.1, verbatim:
  "Let G be a countable discrete MF-group that admits a γ-element (e.g. G is
  uniformly embeddable in a Hilbert space). If H^{2k}(G, Q) ≠ 0 for some
  k ≥ 1, then G is not matricially stable."  For `K` the hypotheses on `G`
  hold: `K` is residually finite (a knot group), and it is a-T-menable,
  being virtually `F_6 × Z`.  But `H^(2k)(K; Q) = 0` for all `k >= 1`.  The
  relator is not a proper power, so the presentation complex is aspherical
  (Lyndon) and of dimension 2.  Its Euler characteristic is `1 - 2 + 1 = 0`
  and `b_1 = 1`, so `b_2 = 0`.  The determinant-winding invariant of ESS
  Theorem 3.9 also gives nothing.  The relator `x^4 y^(-3)` is not
  homogeneous, and scalar phases on `A` and `B` adjust `det(A)^4 det(B)^(-3)`
  freely, since `gcd(4, 3) = 1`.

## Why it is not easy

- **One-sided correction fails.**  Put `U = A^4` and look for `B'` near `B`
  with `B'^3 = U`.  This can fail even when `A^4 = 1` exactly.  Take
  `A = diag(1, i)` and `B` a cube root of `exp(i eps sigma_x)`, where
  `sigma_x` is the Pauli matrix.  Any `A'` with `A'^4 = B^3` commutes with
  `B^3`.  That has distinct eigenvalues `e^(± i eps)`, so `A'` is diagonal
  in the `sigma_x` basis and stays at distance at least `|1 - i|/2` from
  `A`.  So `A` and `B` must be corrected jointly.
- **The ESS method does not apply.**  The ESS proof for `pg` goes through
  `pg` being virtually abelian, which makes `C^*(pg)` a two-dimensional
  NCCW complex, and then through Eilers-Loring-Pedersen.  `K(3,4)` is not
  virtually abelian.  `C^*(K)` is a `C(S^1)`-algebra over `sp(c)`.  Each
  fibre is the full free product `C^4 * C^3 = C^*(Z/4 * Z/3)`, which is
  semiprojective (Blackadar).  Going once around the circle twists the
  fibre by `alpha -> i alpha`, `beta -> e^(2 pi i/3) beta`.  This is a
  heuristic description and is used nowhere.  The difficulty is the one
  recorded in the w16 attempt on
  `lifted-thompson-t-centre-has-commutant-eigencorners`: `sp(A_n^4)` fills
  arcs, and `B_n` can mix nearby spectral subspaces.
- **Literature.**  No operator-norm stability result for torus knot groups
  was found.  Hadwin-Shulman (arXiv:1706.08405, Theorem 10) prove only
  Hilbert-Schmidt stability, verbatim: "One-relator groups with a
  nontrivial center are II 1-factor stable."  The trace route cannot give
  corona conclusions, by the EL20 trace kill.

## What a refutation looks like

A refutation is a sequence of pairs with `||A_n^4 - B_n^3|| -> 0` that stays
a fixed distance from every exact pair.  A natural candidate is the
following.  Take a non-liftable almost representation of `F_6 × Z` of
Voiculescu type, with a nonzero Bott class on some pair
`(generator of Z, free generator)`, and induce it to `K`.  The induced
Bott classes average to zero over `Z/12`, because `H^2(K; Q) = 0`.  So such
a refutation would need an obstruction that is not rational.  For `pg`, ESS
show there is none.

## Attempts

- 2026-09-19 swarm-0917-w16-w16-ptm-follow (stability-approximation).
  - Tried: one-sided correction (keep `A`, take a cube root of `A^4`).  It
    dies at the `diag(1, i)` example above: `A'` is forced to commute with
    `B^3`, which has simple spectrum.
  - Tried: the ESS NCCW route used for `pg = K(2,2)`.  It dies at the first
    step, because `K(3,4)` is not virtually abelian, so `C^*(K)` is not a
    low-dimensional NCCW complex.
  - Tried: a rational obstruction via Dadarlat Theorem 1.1.  It dies
    because `H^2(K; Q) = 0`.
  - Deferred next attack: joint correction fibrewise over `sp(A^4)`, using
    semiprojectivity of `C^*(Z/4 * Z/3)` on arcs, then gluing across the
    twist `alpha -> i alpha`, `beta -> e^(2 pi i/3) beta`.  The gluing step
    is where the arc-spectrum difficulty sits.
