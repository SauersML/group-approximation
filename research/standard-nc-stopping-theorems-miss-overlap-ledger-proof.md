---
rg: 2
id: standard-nc-stopping-theorems-miss-overlap-ledger-proof
kind: route
title: Match the published stopping and rounding hypotheses against the physical spike family
target: standard-nc-stopping-theorems-miss-overlap-ledger
requires:
  - one-anchor-odd-spike-has-a-cheap-reducing-cut
  - localized-loewner-pays-spike-or-boundary
---

Read the cited primary statements with their quantifiers intact.

Parcet--Randrianantoanina fix a filtration and an `L_1`-bounded martingale
before defining Cuculescu's decreasing projections.  Their trace telescoping
uses both `q_k<=q_(k-1)` and the conditional-expectation identity.  An
unordered family of positive contractions is not an input to that theorem.
The two obvious encodings fail for exact structural reasons: generated
algebras give adaptedness without the martingale identity, while a diagonal
amplification gives a cut in `M_N tensor M_d` without product form.

Glebsky's Theorem 4 states `delta(epsilon,k)` and assumes every commutator in
the `k`-tuple is small.  Here `(OSC3)` only controls `[R_(a,i),Q_l]` averaged
over `l`; it implies no hypothesis on two different spike squares.  Neither
the tuple-size dependence nor the absent spike--spike commutators can be
removed by relabelling.  Elek--Grabowski changes HS distance to normalized
rank distance and therefore cannot quarantine a full-rank HS-small tail.

Frieze--Kannan's theorem controls scalar rectangular sums of the residual.
No such rectangle is required to commute approximately with the reflections,
so it cannot be inserted into the cosine--sine correction or the localized
Loewner alternative.

Consequently each import stops strictly before the overlap ledger, while the
two required local ingredients already provide more tailored one-cut
information.  This establishes the stated literature fence without claiming
an impossibility theorem for a new parity-aware stopping construction.
