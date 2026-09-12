---
rg: 2
id: borel-structurability-invariants-are-bernoulli-base-blind
kind: claim
title: Invariants of free Borel actions that are monotone under class-bijective maps take one value on the free parts of all full shifts
distinct_from:
  bernoulli-rokhlin-entropy-maximal-for-every-group: that is the open measurable lower bound for Bernoulli Rokhlin entropy; this rules out the whole class of measure-free Borel-structurability invariants as a way to prove it.
  every-group-has-positive-rokhlin-entropy-action: that is the open existence root for positive Rokhlin entropy; this is an established obstruction on Borel invariants, which cannot separate bases at all.
artifacts:
  - research/artifacts/gk-p-inf-wild-borel-and-topological-2026-09-12.md
---

Let `G` be a countably infinite group. Let `J` be an invariant of free Borel `G`-actions with values
in a partially ordered set, such that `J(X) <= J(Y)` whenever there is an equivariant
class-bijective Borel map `X -> Y`. Then `J(Free(q^G))` is the same for every `q >= 2`.

Examples of such `J`: the Borel chromatic number of a Schreier graph, and every Borel
structurability property of the orbit relation.

**Consequence for the entropy lanes.** Over an infinite amenable group the uniform Bernoulli shifts
`q^G` have entropy `log q`, which separates all `q`. No invariant of this class computes entropy, so
none can supply a lower bound for Bernoulli Rokhlin entropy on any host. Together with factor
non-monotonicity (Bowen's weak isomorphism, recorded in the Attempts of
`every-group-has-positive-rokhlin-entropy-action`) and lane `gk-p-inf-cost`'s weak-equivalence
obstruction, a lower bound must be an isomorphism invariant of the measured action. It must be
neither factor-monotone, nor weak-equivalence invariant, nor determined by the Borel class of the
free part.

**ESTABLISHED 2026-09-12** by
[[borel-structurability-invariants-are-bernoulli-base-blind-proof]].
