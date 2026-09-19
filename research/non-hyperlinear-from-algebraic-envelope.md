---
rg: 2
id: non-hyperlinear-from-algebraic-envelope
kind: route
title: Pontryagin duality turns the algebraic envelope of the non-CE relation into the goal group
target: non-hyperlinear-group
requires:
  - algebraic-envelope-principle
  - non-ce-relation-admits-algebraic-action-envelope
  - non-ce-property-t-equivalence-relation-exists
---

`non-ce-property-t-equivalence-relation-exists` supplies the
non-Connes-embeddable tracial factor `L(R)`.
`non-ce-relation-admits-algebraic-action-envelope` places it
trace-preservingly inside `L^infinity(K, Haar) rtimes Lambda` for a
compact second-countable abelian `K` with `Lambda` acting by continuous
automorphisms.  `algebraic-envelope-principle` identifies that ambient
algebra with the group von Neumann algebra of `hat K rtimes Lambda`
under its canonical trace and concludes that this countable discrete
group is not hyperlinear.

Explicitness: with a Haar-linear-subshift base the group
`hat K rtimes Lambda` is finitely generated and recursively presented
(a finitely generated `F_p[Lambda]`-module extension of `Lambda`), and
a Higman embedding upgrades it to an explicit finitely presented
non-hyperlinear group, since hyperlinearity is inherited by subgroups.

This route is disjoint from every stability-flavored lane: it consumes
no HS-stability, no commutant transfer, no trace promotion, and no
finite-dimensional soundness.  Its entire risk is concentrated in the
single envelope hole, which is a von Neumann embedding problem in
ergodic theory, orthogonal to the matrix-approximation walls of the
rest of the frontier.
