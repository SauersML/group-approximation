---
rg: 2
id: operator-unique-neighbor-cosystolic-rounding
kind: claim
title: Operator-valued cosystolic expansion rounds the repeated LDPC presentation on the same Hilbert space
distinct_from:
  unique-neighbor-ldpc-checks-force-dense-noncommutation: that is an exact support theorem; this asks for a dimension-independent normalized-HS correction modulus.
  quadratic-repetition-supports-complete-commutation-overlay: that removes all exact contextual quotients; this is the missing stability statement for approximate representations.
  sparse-clifford-cycles-refute-average-commutator-rounding: that refutes the assertion without parity faces; this includes the LDPC faces in the energy.
---

OPEN.  Choose a bounded-check binary code family whose Tanner complexes have
a uniform operator-valued local-testability/cosystolic constant.  For the
quadratically repeated occurrence reflections, let

```text
E = E_equality + E_local-PVM + E_parity + E_complete-pair. (OUC1)
```

The required condition is a dimension-independent modulus `omega(eps)->0`
such that every tracial matrix representation with `E<=eps` admits, on the
same Hilbert space, a joint PVM `(P_c)_(c in C)` supported on codewords and
coordinate reflections

```text
Q_i' = sum_(c in C) (-1)^(c_i) P_c
```

with average squared normalized-HS displacement at most `omega(eps)` from
the occurrence reflections.

This is an operator `1`-cosystolic expansion statement for the presentation
two-complex.  For fixed `j`, the derivation

```text
delta_j(X)=[X,Q_j]
```

linearizes a bounded parity face by the Leibniz rule.  When face defects and
commutators are small, the row `(delta_j(Q_i))_i` approximately obeys the
classical parity checks, up to bounded local and quadratic errors.  A
classical locally testable code estimate can therefore control distance to
an operator-valued code row.  One then still needs the complete-pair or
exterior sampler to kill the resulting Lie-algebra-valued code kernel and a
bootstrap that improves small commutators to zero-distance from a joint PVM.

Ordinary good-LDPC distance and unique-neighbor stopping expansion prove only
`unique-neighbor-ldpc-checks-force-dense-noncommutation`; they do not provide
this norm estimate.  Conversely the parity term in `(OUC1)` is essential:
`sparse-clifford-cycles-refute-average-commutator-rounding` has vanishing
complete-pair energy but stays a constant distance from all commuting
tuples.  Thus the exact new analytic target is an operator-valued LTC plus
kernel-killing bootstrap, not generic almost-commuting stability.
