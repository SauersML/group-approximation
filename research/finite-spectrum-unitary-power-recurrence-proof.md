---
rg: 2
id: finite-spectrum-unitary-power-recurrence-proof
kind: route
title: Apply simultaneous pigeonhole approximation to the eigenphases
target: finite-spectrum-unitary-power-recurrence
requires: []
---

Write the eigenvalues as `exp(2*pi*i*theta_j)`.  Partition the torus into
`Q^d` half-open cubes.  Two of `0 theta,...,Q^d theta` occupy one cube, so
their positive index difference `m` is at most `Q^d` and every coordinate of
`m theta` is within `1/Q` of an integer.  The scalar estimate
`|exp(2*pi*i*x)-1|<=2*pi*|x|` and the spectral norm formula for a normal
matrix give the result.
