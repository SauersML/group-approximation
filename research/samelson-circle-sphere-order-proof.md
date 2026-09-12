---
rg: 2
id: samelson-circle-sphere-order-proof
kind: route
title: Chern-character integrality bounds the adjoint Whitehead product below, and a destabilized bundle bounds it above
target: samelson-circle-sphere-product-has-order-n
requires: []
artifacts:
  - research/artifacts/stw59-nonabelian-unitary-component-groups-2026-09-11.md
---

Under pi_k U(n) = pi_(k+1) BU(n), the Samelson product corresponds up to
sign to the Whitehead product [x_2, x_(2n)] of generators (Samelson 1953).
A map S^2 v S^(2n) -> BU(n) extends over S^2 x S^(2n) exactly when its
Whitehead product vanishes, so bilinearity reduces the claim to deciding
when (x_2, k x_(2n)) extends.

Lower bound. An extension is a rank-n bundle E with c_1=a and
c_n=k(n-1)! b. With a^2=b^2=0, log c(E)=a+k(n-1)! b-k(n-1)! ab, so
ch_(n+1)(E)=±(k/n) ab. The Chern character is integral on S^2 x S^(2n):
the suspension splits it into three spheres, each with an integral Bott
class. Hence n | k.

Upper bound. The stable class (l-1)+n kappa_(2n)+s gamma has total Chern
class 1+a+n! b+(1+s(-1)^n) n! ab. Taking s=-(-1)^n kills c_(n+1).
Trivial lines split off in rank at least n+2. In rank n+1 the only
obstruction to a section is the vanishing Euler class, so the class is an
honest rank-n bundle. It restricts to ±x_2 and ±n x_(2n), so the case
k=n extends. The order is exactly n.
