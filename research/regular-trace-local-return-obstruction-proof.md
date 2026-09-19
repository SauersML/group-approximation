---
rg: 2
id: regular-trace-local-return-obstruction-proof
kind: route
title: Evaluate the forbidden Fourier atom in the left regular representation
target: regular-trace-blocks-exact-local-predicate-return
requires: []
---

Expand `(RTL1)` in the group basis.  Because
`<J,z_1,...,z_k>=(C_2)^(k+1)`, its `2^(k+1)` monomials are distinct.  The
coefficient of the identity is `2^(-(k+1))`; every other monomial is a
nonidentity group element.  The canonical group trace extracts the identity
coefficient, proving `(RTL2)`.

The image of `e_a^-` in `L(Gamma)` is therefore a nonzero projection in a
finite von Neumann algebra.  It cannot be properly infinite.  Every defining
group relator evaluates to the identity in the left regular representation,
so every relator-energy term is zero.  These two observations rule out the
three exact tracial conclusions in the claim.
