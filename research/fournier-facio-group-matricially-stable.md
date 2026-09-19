---
rg: 2
id: fournier-facio-group-matricially-stable
kind: claim
title: Matricial stability of the Fournier-Facio torsion-free group
distinct_from:
  map-matricial-stability-non-mf: that claim is the established implication from stability plus minimal almost periodicity; this one is the stability hypothesis itself, for one specific group.
  leavitt-steinberg-hs-stable: that is a stability question for the Steinberg group over a Leavitt-type ring in the Hilbert--Schmidt setting; this is operator-norm matricial stability for the published torsion-free group.
  torsion-free-countable-non-mf: that claim asserts a torsion-free group is not MF; this one asserts a stability property and says nothing about MF on its own.
  fournier-facio-torsion-free-skeleton: that claim is established and records the group's construction and compression core; this one is an unproved analytic property of the same group.
  torsion-free-finitely-presented-non-mf: that root is the non-MF existence statement; this is one analytic prerequisite of one route into it.
  torsion-free-higman-embedding: that claim is a combinatorial embedding theorem; this one is an operator-norm approximation property of a fixed group.
---

The Fournier-Facio group `G` of `fournier-facio-torsion-free-skeleton` is
matricially stable: every asymptotic homomorphism `G -> U(k_n)` is
pointwise-norm close to a sequence of genuine homomorphisms.

## Ideas

This is the analytic hypothesis of `map-matricial-stability-non-mf`, and it
is the only one of the four analytic holes in this cluster that is a
*named property with a literature* rather than a bespoke question.  What is
known cuts both ways and should be held in view together.

- **For.**  Higher-rank lattices are uniformly stable with respect to
  submultiplicative norms (Glebsky--Lubotzky--Monod--Rangarajan,
  arXiv:2301.00476), so Kazhdan groups are not automatically unstable, and
  the mechanism there is cohomological vanishing, which small-cancellation
  quotients of Kazhdan groups may well inherit.
- **Against.**  Dadarlat, arXiv:2007.12655, Corollary 1.3: a countable
  **linear** group with `H^{2k}(G;Q) != 0` for some `k >= 1` is not weakly
  matricially stable.  `G` is not linear — it contains an infinite finitely
  presented simple group, hence is not residually finite
  (`fournier-facio-group-finite-dimensional-shadow`) — so the corollary does
  not apply directly; but its Theorem 1.2 covers weakly quasidiagonal groups
  admitting a `gamma`-element, and whether `G` is in that class is
  unexamined.  Note the tension: if `G` were weakly quasidiagonal and had a
  `gamma`-element, stability would force `H^{2k}(G;Q) = 0` in all nonzero
  even degrees, which is a checkable consequence and a place to look for a
  refutation.
- **Coarse geometry unexamined.**  A `gamma`-element follows from uniform
  embeddability in Hilbert space.  `G` is built by small cancellation over
  an acylindrically hyperbolic group; Gromov monsters show that
  small-cancellation constructions can fail coarse embeddability, but those
  are built from expanders and this one is not.  Nobody has checked.

The honest summary is that this claim is neither supported nor refuted by
anything currently in hand, and that it is the one hole in the cluster where
a literature answer might already exist for a related group.
