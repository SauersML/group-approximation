---
rg: 2
id: identity-return-actuator-gap-proof
kind: route
title: Evaluate the arbitrary-word actuator on the identity return
target: identity-return-makes-arbitrary-actuator-root-strength
requires:
  - finite-game-gap-makes-the-cyclic-acceptance-compressor-strict
artifacts:
  - research/artifacts/identity-return-actuator-quantifier-audit-2026-08-30.md
---

Fix `L>=1` and specialize the prescribed ambient word to `r=1`.  In any
canonical-profile microstate sequence, packet exactification gives projections
`Q_n` with

```text
tr(Q_n) -> alpha > 0
```

and the identity word evaluates to `I).  Therefore

```text
||Q_n I Q_n||_2^2 = ||Q_n||_2^2 = tr(Q_n) -> alpha.
```

But `(ACA1)` gives

```text
limsup_n ||Q_n I Q_n||_2^2 <= alpha rho^(2L) < alpha,
```

because `rho<1`.  The fixed gap `alpha(1-rho^(2L))` cannot be absorbed by
the `o(1)` terms, and an `o_2(1)` packet repair changes neither limit.

Thus no canonical-profile microstate sequence exists for any output satisfying
`(ACA1)` at the identity return.  The conclusion is the stated
vacuity/root-strength dichotomy, not a formal refutation of the existential
claim.
