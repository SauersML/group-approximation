---
rg: 2
id: samelson-circle-sphere-product-has-order-n
kind: claim
title: The Samelson product of the generators of pi_1 U(n) and pi_(2n-1) U(n) has order exactly n
artifacts:
  - research/artifacts/stw59-nonabelian-unitary-component-groups-2026-09-11.md
---

For n>=2, let alpha in pi_1 U(n) be the class of z -> diag(z,1,...,1)
and omega a generator of pi_(2n-1) U(n) = Z. The Samelson product
<alpha,omega> in pi_(2n) U(n) = Z/(n!) has order exactly n.

Equivalently, the commutator of the pullbacks of alpha and omega to
S^1 x S^(2n-1) is a nontrivial class in [S^1 x S^(2n-1), U(n)]: the
group of components of C(S^1 x S^(2n-1), U(n)) is not abelian.

The proof, Section 1 of the attached artifact, uses the adjoint Whitehead
product [x_2, x_(2n)] in pi_(2n+1) BU(n). Integrality of the Chern
character on S^2 x S^(2n) forces n | k whenever the map (x_2, k x_(2n)) extends.
Conversely, a stable class with c_1=a, c_n=n! b and vanishing c_(n+1)
destabilizes to rank n, so the case k=n extends. Bott's general formula
for Samelson products in U(n) is not used.

ROUTES

samelson-circle-sphere-order-proof
