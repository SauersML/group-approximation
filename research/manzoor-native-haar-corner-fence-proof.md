---
rg: 2
id: manzoor-native-haar-corner-fence-proof
kind: route
title: Combine Pontryagin duality, amenable-extension soficity, and corner permanence
target: manzoor-native-haar-envelope-is-ce-after-corners
requires:
  - algebraic-envelope-principle
  - abelian-by-virtually-free-groups-are-sofic
  - free-actor-extensions-cannot-host-nonce-relation
  - manzoor-natural-subgroup-subshift-is-not-a-haar-envelope
  - non-ce-property-t-equivalence-relation-exists
---

Fourier transform gives `(MNC2)`.  Apply
`abelian-by-virtually-free-groups-are-sofic` with the free actor `F`; soficity
implies Connes embeddability of the canonical group factor.  Restricting a
trace-preserving embedding into `R^omega` proves inheritance by von Neumann
subalgebras and corners, while standard matrix amplification proves the
other permanence statements.  The `L^2` projection onto any finite von
Neumann subalgebra gives the trace-preserving normal conditional expectation.

Manzoor Proposition 2.11 and Definition 2.12 identify the GNS algebra inside
the relation algebra.  The normal-ideal argument of
`free-actor-extensions-cannot-host-nonce-relation` proves that the orbit-arrow
quotient `(MNC3)` is singular.  The primary-space audit then excludes the
claim that one of the spaces already used in the paper secretly supplies
the required Haar algebraic base.

