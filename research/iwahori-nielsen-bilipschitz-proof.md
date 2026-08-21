---
rg: 2
id: iwahori-nielsen-bilipschitz-proof
kind: route
title: Telescope the two Nielsen words and use involutivity
target: iwahori-nielsen-hs-bilipschitz
requires: []
---

For unitary pairs representing `pi,rho`, multiplication and inversion are
isometries in normalized HS norm up to telescoping.  The word `u^-1e` has
length two, so its images differ by at most `2d_B(pi,rho)`; the word
`u^-1eu` has length three, so its images differ by at most `3d_B(pi,rho)`.
Taking the maximum proves the forward factor `3`.  The displayed Nielsen
map is an involution, so applying the same estimate to `alpha^*pi,
alpha^*rho` proves the reverse bound.
