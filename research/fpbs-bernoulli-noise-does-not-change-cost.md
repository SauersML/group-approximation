---
rg: 2
id: fpbs-bernoulli-noise-does-not-change-cost
kind: claim
title: Adding independent Bernoulli information to a free action does not change its cost
distinct_from:
  fpbs-aw-finite-pattern-input: that is the imported Abert-Weiss total-variation approximation of a finite label pattern inside a given free action; this one is the cost identity C(a x b) = C(a) for the whole Bernoulli extension and every intermediate factor, proved by applying such a simulation to a graphing-cost-plus-repair score
  fpbs-finite-partition-derandomization: that is the selector-and-repair measure estimate used in the torsion repair constructions; this one is a statement about action costs under a Bernoulli extension, and its simulation lemma keeps all pre-existing base data fixed while colouring a separating finite partition
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/responses/55_0909-215618.md
---

For a free action a of a finitely generated group and a Bernoulli shift b, C(a x b) = C(a), and every intermediate factor between them has the same cost. This is a consequence of established weak-containment theory rather than a new theorem: the Bernoulli extension is weakly equivalent to the original action and cost is monotone under weak containment. The direct proof isolates the mechanism. Given a finite subset F, a finite alphabet with law lambda, and a bounded measurable score h on X x K^F, there is a measurable colouring c of X with the F-window score at most the product-law average plus delta: separate the translates xg, g in F, by a finite measurable partition outside a small exceptional set and colour its atoms independently, so at a good root the tested colours have exactly the product law while all pre-existing base data in h stay fixed. Applying this to the cost-plus-failed-request score of a truncated near-optimal graphing on a x b, after cylinder approximation of its domains, gives C(a) <= C(a x b); lifting gives the reverse.

The simulation does not produce independent labels at all orbit coordinates at once, and it does not sample group-coherent source states independently at different vertices; such sampling need not define the original extension or preserve its routing certificates. This removes a whole class of possible information effects, for every finitely generated group.

Status records a written deduction over imported theorems, not independent validation.
