---
rg: 2
id: samelson-odd-sphere-orders-proof
kind: route
title: Chern-character integrality on S^(2i) x S^(2j) and a destabilized bundle with c_(n+1)=0 give order n·C(n-1,i-1)
target: samelson-odd-sphere-products-in-u-n-orders
requires: []
artifacts:
  - research/artifacts/stw59-samelson-orders-and-wedged-arms-2026-09-11.md
---

Pass to the adjoint Whitehead product [x_(2i), x_(2j)] in pi_(2n+1)BU(n).
The map (x_(2i), k x_(2j)) extends over S^(2i) x S^(2j) exactly when that
product, times k, vanishes.

Necessity: an extension has c = 1 + A + B, with A = ±(i-1)! a and
B = ±k(j-1)! b. Then log c = A + B - AB, so ch_(n+1) = ±(k/N) ab. The
Chern character is integral on S^(2i) x S^(2j), hence N divides k.

Sufficiency: the stable class κ + N κ' + γ has total Chern class with
vanishing ab coefficient, because N(i-1)!(j-1)! = n!. Trivial lines split
off above rank n+1. In rank n+1 the only obstruction is c_(n+1) = 0, so
the class is a rank-n bundle restricting to ±x_(2i) and ±N x_(2j).
