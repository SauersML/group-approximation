---
rg: 2
id: odd-leavitt-stationary-xor-proof
kind: route
title: Realize prefix reflection refinement by the regular affine Boolean action
target: odd-leavitt-reflections-retain-stationary-xor-overlap
requires:
  - odd-leavitt-steinberg-reflection-prerequisites
  - leavitt-crossed-gram-pauli-charge-has-sectorwise-escape
---

For orthogonal `P,E`, direct multiplication gives `(OLX2)`.  The group in
`(OLX4)` is the affine group of the two-dimensional Boolean space.  The
linear transvection `d |-> de`, `e |-> e` is involutive, proving
`(OLX5)` and hence the connector relation in the reverse direction.

In a finite-group regular trace every nonidentity group element has trace
zero.  Expanding `(OLX6)` therefore gives the three half-traces in `(OLX7)`;
expanding `P'E'=(1-d-e+de)/4` gives `1/4`.  Expansion of the product
reflection gives `(OLX8)`.  This is already an amplification-stable zero-
defect countermodel to inference of projection inclusion.

At depth `N`, take the probability space `F_2^(2^N)`.  Multiplication by the
character belonging to the sum of the descendant leaf coordinates realizes
each prefix reflection.  Parent equals child-product exactly.  Linear
changes of leaf coordinates give the required Koopman actor unitaries.

Finally apply the four-sector construction `(LPG3)` separately in every
selector sector.  A finite actor merely permutes a finite collection of such
charts; inducing over that orbit and permuting one private gauge qudit per
crossed incidence makes every covariance relation literal.  The inverse
gauge commutator cancels only the unwanted overlap phase, so the designated
common `p`-phase relations can be retained on independent label qudits.
This proves the asserted fixed-depth crossed-Pauli extension.  No statement
about a uniform infinite incidence or a coefficient-algebra decoder is used.

