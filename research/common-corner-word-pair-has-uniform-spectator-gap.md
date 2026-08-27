---
rg: 2
id: common-corner-word-pair-has-uniform-spectator-gap
kind: claim
title: The common-corner packet words have a dimension-free joint spectator gap
refuted_by: amplification-natural-word-pairs-have-no-scalar-joint-gap
distinct_from:
  quantum-expander-relative-commutant-rounding: that rounds to the full multiplicity commutant of one growing matrix factor; this must reduce the commutant of both named factors together to the scalar line.
  full-packet-bicommutant-synchronization: that tests one transported carrier against every unitary in a packet commutant; this asks a bounded word-exposed joint actor to detect every non-scalar spectator operator.
  kazhdan-transitive-pauli-actor-localizes-one-mixed-word: that transports a supplied mixed Weyl commutator across a scalable Pauli orbit; this requires the resulting joint action to have no invisible multiplicity summand.
---

On the same positive-density spectral corner `P` used for packet
exactification and cross-Gram alignment, exhibit a bounded family `S` of
named packet/reservoir words and a constant `kappa>0`, independent of the
matrix size and reservoir rank, such that every `Y in P M_d P` satisfies

```text
||Y-tau_P(Y)P||_2
 <= kappa^(-1)
    (sum_(s in S) ||[Y,s]||_2^2)^(1/2).                 (CSG1)
```

Here the words in `S` must belong to the two exactified named algebras on
`P`; the estimate is required after the same `o(1)` corner change used by
the gauge decoder.  In particular their joint commutant is scalar, so the
two commuting algebras jointly generate `P M_d P`.  This is the minimal
robust spectator-elimination input absent from one cross-Gram overlap plus
two Pauli commutators.

The zero-defect algebraic criterion would only ask that the joint commutant
be scalar.  The uniform inequality `(CSG1)` is the quantitative form needed
to pass from vanishing normalized-Hilbert--Schmidt word defects through
corners of growing dimension.

**REFUTED for the stated all-microstate word-natural interface.**  Tensor
amplification preserves the corner and every named word but inserts a full
matrix algebra into their joint commutant.  A viable replacement can only
bound distance to the actual joint commutant, as in `(ANJ2)` of
`amplification-natural-word-pairs-have-no-scalar-joint-gap`; it yields tensor
factors modulo a common spectator, not `(CCMB1)` in the full ambient corner.
