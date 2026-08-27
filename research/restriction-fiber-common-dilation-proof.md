---
rg: 2
id: restriction-fiber-common-dilation-proof
kind: route
title: Cross-add the positive and negative irreducible multiplicity parts
target: restriction-fiber-orbits-have-optimal-common-dilation
requires:
  - congruence-endpoint-orbits-are-restriction-ring-fibers
---

Since `res(m)=res(n)`, subtracting the common coordinatewise part gives
`res(p)=res(q)`.  Equality of total dimensions gives
`|p|_dim=|q|_dim`.  Equation `(RFD2)` is immediate.

For optimality, at every coordinate where `m_gamma>n_gamma`, an equality
`m+u=n+v` forces `v_gamma>=p_gamma`; the opposite coordinates similarly
force `u>=q`.  Weighted summation proves the lower bound.  Equation `(RFD4)`
is `(ERF4)` from the required claim, and rearranging proves the stated
quadratic bounds.

