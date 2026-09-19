---
rg: 2
id: rf-reynolds-mask-energy-countermodel-proof
kind: route
title: Separate every mask support and canonical word in one finite quotient
target: rf-reynolds-mask-deficit-is-not-relator-energy
requires: []
---

Let `T` contain `W` and every nonidentity group element occurring in the
support of some `q_j`.  Residual finiteness gives a finite quotient
`phi:Gamma->Q` for which no element of `T` maps to the identity.  Evaluate in
the normalized left regular representation of `Q`.  Every defining relator
is exact and every `w in W` has trace zero.  Also

```text
tr_Q(phi(q_j))
```

is the coefficient of the identity in `phi(q_j)`.  By the choice of `Q`, no
nonidentity support element contributes to that coefficient, so it equals
the identity coefficient `tau_Gamma(q_j)`.  This proves `(RME3)` and refutes
`(RME2)`.

For `(RME5)`, the identity coefficient of the standard central idempotent
`z_chi` is `(dim chi)^2/|H|`.  If the quotient is injective on `H`, the same
calculation is equivalently the Plancherel multiplicity of `chi` in the
regular representation.  Finally, in any exact finite-dimensional
representation the right side of `(RME2)` is zero and each left summand is
nonnegative; hence every `1-q_j` must vanish, proving the radical statement.
