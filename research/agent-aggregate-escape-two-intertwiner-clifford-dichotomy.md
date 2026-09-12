---
rg: 2
id: agent-aggregate-escape-two-intertwiner-clifford-dichotomy
kind: claim
title: A two-intertwiner support cell reduces exactly to a twisted stabilizer representation
distinct_from:
  agent-aggregate-escape-finite-packet-actor-no-go: that treats honest finite-packet semidirect actions; this allows a phase-sensitive relation between two intertwiners and identifies its complete projective obstruction.
  existential-cycle-gauge-absorbs-square-and-reynolds-readouts: that varies a free chord inside the packet commutant; this classifies what remains after arbitrary holonomy relations constrain that commutant gauge.
  agent-aggregate-escape-rfd-support-orientation-firewall: that says ACO4 requires an HS finite-dimensional radical; this identifies the precise central extension in which that radical would have to occur.
---

**ESTABLISHED CLIFFORD DICHOTOMY.**  Let `F` be a fixed finite joint packet
(it may contain two contexts and their shared marginal), let

```text
Q=<s,t | R>
```

act on `F` by automorphisms, and form the corresponding covariance
presentation.  Fix an irreducible packet type `sigma`.  Its `Q`-orbit is
finite.  Let `Q_sigma` be its stabilizer and choose packet intertwiners
`V_q`, `q in Q_sigma`.  They define a finite-image multiplier

```text
V_q V_r=omega(q,r)V_(qr).                               (TCF1)
```

Then a finite-dimensional representation of the full covariance/holonomy
presentation whose restriction to `F` contains `sigma` exists **if and only
if** the inverse twisted stabilizer algebra

```text
C_(omega^(-1))[Q_sigma]                                 (TCF2)
```

has a nonzero finite-dimensional star representation satisfying the imposed
holonomy relations.  Given such a multiplicity representation `M`, the
honest stabilizer operators are `V_q tensor M_q`; induction over the finite
orbit `Q/Q_sigma` gives the full representation.  Conversely, restricting
any full representation to the `sigma`-isotypic multiplicity space extracts
exactly such an inverse projective representation.

This completely audits a relation between two packet intertwiners.

## Finite-holonomy countermodel

If the holonomy seen by `(TCF1)` factors through a finite quotient `H` of
`Q_sigma`, then `(TCF2)` always has a finite-dimensional representation: use
the inverse-twisted left regular representation of `H`.  Hence the marked
packet type survives after three bounded operations:

```text
finite orbit sum  +  inverse-cocycle tensor  +  arbitrary direct sums. (TCF3)
```

All covariance rows and the relation between `s,t` are exact.  If
`T e_i!=0` on `sigma`, the induced representation has positive
`sum_i ||T e_i||_2^2`; amplification preserves its normalized density.
Thus no finite holonomy, finite Schur multiplier, finite triangle-face
packet, or finite projective two-cell can imply `(ACO4)`, even when it is
phase sensitive and genuinely crosses two contexts.

## Exact surviving condition

To exclude `sigma`, an infinite holonomy quotient must be chosen so that the
central extension representing `omega` has no finite-dimensional
representation with the required inverse central character.  To prove
`(ACO4)` one needs the robust form: every approximate finite-dimensional
inverse-projective representation must have the marked character carrier
bounded by `C sqrt(E)`.

Therefore a two-intertwiner construction does not avoid the HS-radical gate.
It relocates it verbatim to one explicit twisted stabilizer algebra.  A
nonamenable actor, property `(T)`, or a nontrivial Schur multiplier is not
enough; the required input is a **quantitative projective fd-radical** for
`Q_sigma`.  Supplying that input while the perfect tracial BCS model has zero
forbidden carrier would finish `(ACO4)`, but it is the new theorem rather
than a consequence of finite holonomy.

DERIVATION
agent-aggregate-escape-two-intertwiner-clifford-dichotomy via agent-aggregate-escape-two-intertwiner-clifford-proof
