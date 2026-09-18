---
rg: 2
id: view-local-selectors-beat-one-half-through-non-honest-witnesses
kind: claim
title: Some parity-faithful view-local branch selector on gauge-randomised Grassmann 2-to-1 YES instances has orientation-lift value at least 1/2 + gamma through labellings that are not honest labellings of a small equivariant witness menu
distinct_from:
  view-local-branch-selectors-are-gauge-blind: that bounds honest lift value over subexponential equivariant menus; this asks whether the full lift value, a maximum over all labellings, escapes that bound.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that keeps honest certificates and gives up locality of views; this keeps locality and gives up honest certificates.
---

**OPEN.** This is heretic denial H2.

**Assumption denied (A2).** The HOT families assume the completeness witness is
canonical: one planted or honest labelling (or its gadget encoding) certifies
YES value. All the design effort then goes into supplying richness and soundness
at gadget level, because completeness is inherited. The orientation lift inverts
this. Richness and soundness come free, and completeness is the whole problem.
The denial is that completeness above one half is witnessed by labellings that
are not honest, or by an exponentially rich, unclustered menu.

**Claim.** There are `gamma > 0`, a Grassmann 2-to-1 reduction `D` from gap-3LIN,
and a view-local selector `S` with parity leakage `w_bad(S) = o(1)` and
`s = O(1)`, such that for every YES input `I` and most gauges `z`,
`val(U_(S(I^z))) >= 1/2 + gamma`.

**Why it is the exact complement of the kill.** By
`view-local-branch-selectors-are-gauge-blind`, the honest labellings of any
equivariant menu of size `exp(o(n/s^2))` reach at most `1/2 + o(1)` on most
gauges. So a witness for this claim is necessarily one of two kinds:
- a labelling whose A- and B-labels are not restrictions of one assignment
  satisfying the window equations, for example a zoom-structured or
  vertex-wise mixed labelling;
- an honest labelling drawn from `exp(Omega(n/s^2))` well-separated
  assignments.

**Falsifiers.**
- (i) A structure theorem that every lift labelling of value `>= 1/2 + gamma`
  on a YES instance agrees on `gamma'(gamma)` of the edge weight with an honest
  labelling from an equivariant menu of `exp(o(n))` clusters. Combined with the
  kill, this refutes the claim.
- (ii) A computation on small DKKMS windows (`k <= 2`, `l <= 3`) of
  `max_labelling val(U_o)` for radius-1 view-local selectors, averaged over
  gauges, showing a maximum of `1/2 + o(1)`.

## Attempts

* **Honest certificates (2026-09-18).** **Dead as a witness type.** Honest
  labellings from equivariant menus of size `exp(o(n/s^2))` reach at most
  `1/2 + o(1)` on most gauges (`view-local-branch-selectors-are-gauge-blind`,
  Theorem 2). Falsifier (ii) is deferred: the exact lift value is a maximum over
  `2^(#B-vertices * 2^(l-1))` labellings. That is feasible only for toy windows
  with a handful of B-vertices, where locality is vacuous.
