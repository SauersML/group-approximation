---
rg: 2
id: agent-aggregate-escape-two-intertwiner-aco4-is-twisted-nonce
kind: claim
title: A quantitative two-intertwiner support row already makes its stabilizer twist non-CE
distinct_from:
  agent-aggregate-escape-two-intertwiner-clifford-dichotomy: that classifies exact finite-dimensional extensions by inverse projective stabilizer representations; this upgrades the classification to matrix microstates and Connes embeddability.
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that gives the global existential equivalence; this identifies the particular twisted factor hidden inside any successful ACO4 holonomy cell.
  agent-aggregate-escape-central-support-orientation-terminal: that turns ACO4 into a nonhyperlinear group using the BCS gap; this shows a two-intertwiner proof of ACO4 has already crossed the same frontier inside its holonomy stabilizer.
---

**ESTABLISHED QUANTITATIVE FENCE.**  Use the notation of
`agent-aggregate-escape-two-intertwiner-clifford-dichotomy`.  Suppose the
finite-packet covariance presentation has a forbidden packet type `sigma`
with `T e_i!=0`, and suppose its proposed two-intertwiner relations imply
the normalized-HS support estimate `(ACO4)`.

Then the inverse twisted stabilizer von Neumann algebra

```text
L_(omega^(-1))(Q_sigma)                                 (TNC1)
```

is not Connes embeddable.

Indeed, if `(TNC1)` were Connes embeddable, take matrix microstates for its
twisted regular trace.  Tensor them with the fixed packet intertwiners
`V_q`, whose multiplier is `omega`, so the two cocycles cancel.  Induce over
the finite orbit `Q/Q_sigma`.  Fixed-word telescoping turns these into
finite-dimensional approximate representations of the full
packet/holonomy presentation with relator energy tending to zero.  The
packet factor is exact and fixed, so the induced normalized trace of the
marked forbidden corner is a constant

```text
c_sigma>0                                               (TNC2)
```

independent of the microstate dimension.  This contradicts `(ACO4)`.

Thus a successful genuinely cross-context two-intertwiner cell is not a
smaller matrix trick.  It has constructed a non-CE twisted group factor.
By `twisted-factor-existence-is-equivalent-to-nonhyperlinearity`, existence
of `(TNC1)` is already equivalent to existence of a nonhyperlinear group.  If
`omega` is finite valued, the associated finite central extension is the
explicit group witness via `thom-central-corner-criterion`.

This also rules out all three dilution operations at the approximate level:

1. finite orbit induction only changes `(TNC2)` by a fixed factor;
2. tensoring is exactly how the inverse cocycle is canceled and preserves
   the packet density;
3. direct sums of twisted microstates preserve both vanishing normalized
   defect and the positive normalized marked density.

Consequently the only noncircular use of the BCS input would be to prove
non-embeddability of `(TNC1)` *from the shared contextual relations*.  That
is precisely the missing groupification of the non-CE tracial obstruction,
now expressed as one twisted stabilizer factor.  Choosing a pre-existing
nonamenable, Kazhdan, Higman, triangle, or proper-corner holonomy does not
establish it.

DERIVATION
agent-aggregate-escape-two-intertwiner-aco4-is-twisted-nonce via agent-aggregate-escape-two-intertwiner-twisted-microstate-proof

