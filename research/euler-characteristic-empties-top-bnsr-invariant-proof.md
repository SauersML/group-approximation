---
rg: 2
id: euler-characteristic-empties-top-bnsr-invariant-proof
kind: route
title: Nonzero Euler characteristic puts every rank-one local system in the characteristic varieties, so the tropical bound empties Sigma^d
target: euler-characteristic-empties-top-bnsr-invariant
requires: []
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-top-range-2026-09-13.md
---

Full proof in the artifact, Section 3 (two independent proofs).

*Proof A.* For every rank-one local system `rho`, the twisted cellular chain
complex of `X` has the ranks of the cellular complex, so
`sum_{i=0}^{d} (-1)^i dim H_i(X; C_rho) = chi(X) != 0`. Some `H_i(X; C_rho)` with
`i <= d` is nonzero, so the union `V^{<=d}(X)` of the characteristic varieties
in degrees `<= d` is the whole character group and its tropicalization is all
of `H^1(X, R)`. Suciu, arXiv:2010.07499v2, Theorem 1.1:
`Sigma^q(X,Z) <= S(Trop(V^{<=q}(X)))^c`. With `q = d` the right side is empty.
For `X = K(G,1)`, `Sigma^d(X,Z) = Sigma^d(G;Z)`, which contains `Sigma^d(G)`
(Bieri–Renz).

*Proof B.* Novikov–Sikorav vanishing in all degrees makes the Novikov chain
complex split. The identity-coefficient map `tau(sum n_g g) = n_1` is a trace
on the Novikov ring, because below each level of the character a series has
finitely many terms. Applied to the isomorphism between even and odd chain
modules, the trace gives `chi(X) = 0`.
