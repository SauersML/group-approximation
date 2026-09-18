---
rg: 2
id: fpbs-bernoulli-lower-bound-from-cost-lsc
kind: route
title: Lower semicontinuity of cost at the uniform Bernoulli shift measure gives the Bernoulli lower bound for every free action
target: fpbs-free-action-cost-at-least-bernoulli-cost
requires:
  - fpbs-fixed-price-iff-cost-lsc-at-bernoulli
  - fpbs-cost-lsc-at-bernoulli-shift-measures
---

**Restatement note.** The prerequisite `fpbs-cost-lsc-at-bernoulli-shift-measures` is equivalent
to the target, by `fpbs-fixed-price-iff-cost-lsc-at-bernoulli` together with Abert–Weiss
maximality. So this route relocates the target rather than weakening it. The problem moves to
one point `lambda^G` of the compact space of shift measures, where the counterexample normal form
is a race between cheap certificates and convergence of Seward models.

**Deduction.** Let `G` be infinite and finitely generated. By
`fpbs-cost-lsc-at-bernoulli-shift-measures`, item 2 of `fpbs-fixed-price-iff-cost-lsc-at-bernoulli`
holds for `G`, so `G` has fixed price. In particular `C(a) = C(b) >= C(b)` for every free `a` and
every nontrivial Bernoulli `b`.

**Where it dies, if it dies.** It dies at its one prerequisite exactly when some free ergodic
finite-alphabet action has cost below Bernoulli cost. That prerequisite cannot be proved through
window-local bounds (`fpbs-window-local-cost-lower-bounds-fail-at-bernoulli`). The route differs
from `fpbs-bernoulli-lower-bound-from-cycle-tails` and `fpbs-bernoulli-lower-bound-from-reuse-removal`.
Those control certificates of `lambda^G` itself; here the certificates to control belong to the
approximating models.
