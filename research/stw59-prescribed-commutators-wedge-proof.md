---
rg: 2
id: stw59-prescribed-commutators-wedge-proof
kind: route
title: Wedge odd-sphere arms of equal dimension, read independent Euler coordinates and armwise Samelson commutators, and pass to the simple tower
target: stw59-prescribed-commutator-component-groups
requires:
  - samelson-odd-sphere-products-in-u-n-orders
  - gauge-components-over-circle-sphere-towers
  - stw59-exact-finite-abelian-unitary-component-groups
artifacts:
  - research/artifacts/stw59-samelson-orders-and-wedged-arms-2026-09-11.md
---

The arms are M_α = S^(2i_α-1) x S^(2j_α-1) x CP^(e_α), with
bundles 1^(n_α) + L^(e_α), all of dimension 2R; wedge them at based
zero-cells. The circle-sphere finite-stage prerequisite runs verbatim on
each arm. The collapse to S^(2n_α) has degree one, so the arm's Euler
image is n_α! Z and its kernel is central.

The finite-abelian prerequisite supplies the rest of the wedge argument:
top cohomology splits over the arms, and collapsing all other arms gives
attaining classes with one nonzero coordinate. So the central kernel is
direct-sum Z/n_α! and each arm restriction detects one coordinate.

The commutator on arm α factors through the collapse as
<a_(i_α), a_(j_α)>, which has order N_α by the Samelson prerequisite.
Distinct arms meet only at the wedge point, where the generators are 1.

Tautological blocks multiply coordinates by ±1, so the dense-tail twisted
tower is injective on components and an isomorphism on kernels. The limit
arguments (simplicity, unique trace, stable rank two, continuity of K1) are
those of the circle-sphere limit.
