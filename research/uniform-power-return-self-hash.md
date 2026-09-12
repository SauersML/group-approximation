---
rg: 2
id: uniform-power-return-self-hash
kind: claim
title: Finitely compile every conjugacy-to-power challenge with one operator-norm budget
root: true
distinct_from:
  self-hashing-expander-collision-presentation: that asks for recursive Pauli packets, cross-edge checks and an expander checksum; this asks only for one cursor and one uniformly certified family of power returns.
  coprime-power-pair-phase-hnn-is-residually-finite: those exact power-conjugacy cells still have finite models and therefore do not provide a uniform relator-area bound over all exponents.
  conjugacy-addressed-opnorm-challenges-are-lossless: literal conjugacy has zero loss, but the missing semantic comparison to `w^m` is exactly this node.
---

Construct a finite presentation `Gamma=<S|R>`, a nontrivial zero-abelianization
cursor `w`, words `a_m`, and one finite constant `C` such that for every
dimension, unitary tuple and `m>=2`,

```text
||a_m(U) w(U) a_m(U)^-1 - w(U)^m||_op <= C Def_R(U).
```

This analytic inequality target is OPEN. Abstract identities such as those
in `Aff(Q)` do not suffice: their derivation constants may grow with `m`,
and finite models show that some growth must occur there.
A literal conjugate of one of finitely many fixed checks cannot
certify the complete return for all exponents:
`power-return-certificates-have-linear-area` proves a linear lower
bound on total certificate area for every nontrivial free word,
including zero-abelianization cursors. This rules out the bounded-area
implementation, not the purely analytic inequality above.

## Attempts

Exact affine and Baumslag--Solitar-style power conjugacies fail because their
finite models force the derivation constants to grow with the exponent.
Repeated squaring does not avoid the linear lower bound on ordinary
relator area, regardless of circuit depth. A one-cell check on a named
terminal word still requires uniform semantic authentication of that
word as `w^m`. The terminal-port route now displays this separate
norm estimate explicitly; it cannot be supplied by bounded total area.
