---
rg: 2
id: proof-carrying-power-return-terminal-authentication
kind: claim
title: A finite cursor machine authenticates every exponent return through one constant-size terminal port
artifacts:
  - research/artifacts/power-return-certificates-have-linear-area-2026-09-08.md
distinct_from:
  conjugacy-addressed-opnorm-challenges-are-lossless: that transports a check already known to be a conjugate of a root relator; this must build the terminal semantic equality to the addressed power.
---

Construct finite syntax which executes repeated squaring for every exponent
`m`, emits a terminal certificate for `w^m`, and makes the discrepancy between
that certificate and an addressed conjugate of `w` a literal conjugate of one
of finitely many root checks.  The certification constant must be independent
of the exponent and execution depth, and an exact infinite model must keep the
cursor nontrivial.

More precisely, writing `c_m` for the terminal word, the literal
port supplies a uniform bound against `c_m(U)`. One must also prove
one constant `C_sem`, independent of `m` and dimension, such that

```text
||c_m(U)-w(U)^m||_op <= C_sem Def_R(U).
```

Together these estimates supply the required complete return bound.
A group-theoretic equality `c_m=w^m` with unbounded derivation cost
does not supply this semantic estimate.

## Attempts

`power-return-certificates-have-linear-area` proves that the total
ordinary relator area of every nontrivial cursor's return grows at
least linearly with the exponent. This applies to commutator cursors
and finitely enlarged presentations. An isolated one-cell port is
not excluded, but its semantic estimate cannot also come from a
bounded-area certificate. The analytic semantic estimate remains
unconstructed.
