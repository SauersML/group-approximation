---
rg: 2
id: samelson-odd-sphere-products-in-u-n-orders
kind: claim
title: For i+j=n+1 the Samelson product of generators of pi_(2i-1)U(n) and pi_(2j-1)U(n) has order n·C(n-1,i-1)
distinct_from:
  samelson-circle-sphere-product-has-order-n: That is the case i=1 (order n), proved over S^1 x S^(2n-1); this covers every pair i+j=n+1, including i=j, where the order can equal the whole group Z/n!.
artifacts:
  - research/artifacts/stw59-samelson-orders-and-wedged-arms-2026-09-11.md
---

Let n>=2 and 1<=i<=n, j=n+1-i, and let a_i and a_j generate
pi_(2i-1)U(n) and pi_(2j-1)U(n). The Samelson product <a_i,a_j> in
pi_(2n)U(n) = Z/n! has order exactly

    N(n,i) = n!/((i-1)!(j-1)!) = n·C(n-1,i-1).

This agrees with Bott's formula <a_i,a_j> = (i-1)!(j-1)!·generator, but
the proof does not use that formula. For example, N(3,2)=6, so the S^3 x S^3
commutator generates all of pi_6 U(3).

ROUTES

samelson-odd-sphere-orders-proof
