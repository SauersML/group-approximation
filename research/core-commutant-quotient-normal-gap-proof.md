---
rg: 2
id: core-commutant-quotient-normal-gap-proof
kind: route
title: Quotient exact kernel gauges, then separate relative lifting from nonlinear truncation
target: core-commutant-quotient-normal-gap-is-relative-liftability
requires:
  - authenticated-core-union-basin-is-relative-liftability
  - exact-cuspidal-hadamard-mixing-has-macroscopic-cross-blocks
  - congruence-cross-type-mixing-has-uniform-polar-repair
  - tangent-green-divergence-is-flexibly-rank-paid
---

For a fixed core, `one-core-endpoint-union-is-one-finite-restriction-fiber`
identifies the exact zero set with the finite union of core-commutant orbits.
The Hadamard claim proves that no smaller prelabelled packet quotient is
valid.  Taking distance to this full union gives `(CQN2)`.

Apply `authenticated-core-union-basin-is-relative-liftability` to a
vanishing-energy sequence.  It identifies positive limiting flexible
distance to this union exactly with failure of an almost-full coordinate
congruence lift, proving `(CQN3)--(CQN4)`.  If a lift is supplied, apply the
uniform congruence bimodule gap and polar repair to the two genuine endpoint
representations.  This also proves why applying property `(tau)` before the
lift is circular: one of those two representations does not yet exist.

Finally apply the tangent Green/truncation claim at the selected endpoint.
It gives the operator-small normal estimate and pays coordinatewise hard
tails by rank, but explicitly does not show that the hard-tail cut preserves
the exact core.  This proves the stated two-way remainder without asserting
the missing legal truncation.
