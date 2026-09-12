---
rg: 2
id: compatible-heisenberg-density-firewall-proof
kind: route
title: Combine the Schrodinger tower with the cyclic Leavitt trace floor
target: compatible-heisenberg-densities-do-not-imply-leavitt-corners
requires:
  - finite-tags-do-not-atomize-heisenberg-schrodinger-tower
  - heisenberg-sector-is-schrodinger-times-free-multiplicity
  - coherent-heisenberg-decoder-is-marked-nonhyperlinearity
---

In the standard Schrodinger tower, restriction from rank `N+r` to rank `N`
is `p^r` copies of the rank-`N` representation.  The common nontrivial
central carrier is the identity, whereas each polarized character atom has
normalized trace `p^(-N)`.  The restriction commutant contains `U(p^r)`;
a trace-zero cyclic shift in this factor has squared normalized
Hilbert--Schmidt distance two from the identity and preserves all scalar
branching data.

The Weyl operators form an orthonormal basis of the refinement matrix
factor.  The corresponding `p^(2r)` return channels therefore have mutually
orthogonal initial Grams and sum to the whole source Reynolds projection.
They realize the entire rectangular multiplicity reservoir, not an
identified square return.

If the compatible densities alone implied the four Leavitt contractions on
a nonzero corner, `(CHD3)` would give `1<=o(1)`.  This contradiction proves
the claimed density-only firewall while leaving open additional
full-presentation occurrence hypotheses.
