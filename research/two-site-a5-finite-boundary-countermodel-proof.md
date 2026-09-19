---
rg: 2
id: two-site-a5-finite-boundary-countermodel-proof
kind: route
title: Move the marked A5 pair to an independent pair in a finite regular packet
target: two-site-a5-center-has-exact-boundary-countermodel
requires:
  - two-site-a5-plancherel-center-separates-mark
  - bernoulli-center-measurement-retains-boundary-interference
---

The covariance relation in `(ABC3)` follows from
`P_g lambda_B(b) P_g^*=lambda_B(g.b)`.  The tensor factor
`lambda_H(g)` makes the character vanish on the nontrivial actor coset, so
the representation has the canonical character of `B semidirect H`; its
dimension is also the order of that group.

The regular trace on `B=A5^Y` makes the four center labels independent with
one-site law `(ABC4)`.  Since `g^(-1){p,q}={r,s}`, the block-mass coupling
between the measured source and target labels is the product law `(ABC6)`.
Composing a product coupling with itself leaves the product coupling.  For a
probability vector `nu`, the total-variation distance between
`nu tensor nu` and `Diag(nu)` is `1-sum nu_i^2`; substituting
`nu=mu tensor mu` gives `(ABC7)`.

