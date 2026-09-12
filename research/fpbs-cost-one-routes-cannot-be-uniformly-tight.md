---
rg: 2
id: fpbs-cost-one-routes-cannot-be-uniformly-tight
kind: claim
title: Nonamenability prevents uniformly tight routes in near-unit-degree connected invariant subgraphs
invalidates:
  - fpbs-dead-uniform-tight-routes-contradiction
  - fpbs-dead-limit-graphing-connectivity
distinct_from:
  fpbs-quantitative-routing-tail-bound: that is the quantitative expansion bound, giving an explicit averaged tail at every fixed radius and a logarithmic mean-length rate; this is the qualitative impossibility of uniform tightness and names no rate.
---

**Statement.** Proposition 5 of the percolation note: let G be a Cayley graph of a nonamenable
finitely generated group and let H_n be invariant random connected spanning subgraphs with
(1/2) E deg_{H_n}(o) tending to one. Then it is impossible that d_{H_n}(o,s) is uniformly tight in n
for every generator s. In particular those expectations cannot be uniformly bounded. Cost can approach
one, but the routes that express the original generators must get long.

**Proof location.** `research/artifacts/fpbs/fixed-price-percolation.md`, Section 7, Proposition 5;
response 1. Two independent routes now reach it. The compactness route takes a weakly convergent
subsequence in {0,1}^{E(G)}; expected root degree and the cylinder events d_H(o,s)<=R both pass to the
limit, so uniform tightness makes the limit connected almost surely with half expected root degree one.
Multiplying by a free Bernoulli action produces a free action with an attained cost-one graphing, which
contradicts the amenability theorem. The quantitative route applies the tail inequality of
`fpbs-quantitative-routing-tail-bound` with delta_n tending to zero at each fixed R; the limiting lower
bound h/d is positive and independent of R, which uniform tightness would contradict.

**Imported inputs.** Gaboriau, *What is... cost?*, arXiv:1011.2294v1, the paragraph after the
Ornstein-Weiss discussion: a free action with an attained cost-one graphing forces the group to be
amenable. The identifier resolves. The distinction matters here and is respected: the infimum being one
is not enough, attainment is what the contradiction needs.

**Finite-replay evidence.** For the compactness route, none, and none is available: the argument is a
weak-limit argument in an infinite product. For the quantitative route, the 184,096 pointwise checks of
`routing-bound-replay.json`.

**Prior statement of the same obstruction in this repository.**
`notes/TRUE_ROUTED_HOLONOMY_PHASE_REPAIR.md` is the note the external session
read first (response 1, Section 1). It already identifies the phenomenon:
driving a graphing's cost toward one does not control the lengths of the paths
needed to express the original generators, and its corrected argument
therefore carries extra routing and phase-compatibility hypotheses, explicitly
withdrawing the unconditional cost-one shortcut. Proposition 5 above is the
percolation-side quantitative form of that withdrawal. The note is a
noncanonical prior record, not a proof input, and is not cited in `artifacts:`.

**Evidence level.** Written deduction from one verified import, now with a second and quantitative
derivation. Not refereed, not formally verified. It is an obstruction, so it constrains constructions
rather than advancing either goal.
