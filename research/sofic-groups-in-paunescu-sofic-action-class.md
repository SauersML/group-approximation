---
rg: 2
id: sofic-groups-in-paunescu-sofic-action-class
kind: claim
title: Every p.m.p. action of a sofic group is sofic (Paunescu's question)
root: true
refuted_by:
  - kun-thom-free-nonsofic-action
distinct_from:
  kun-thom-free-nonsofic-action: that is the established free counterexample; this is the universal statement it refutes
  paunescu-sofic-action-class-permanence: that records the classes of groups proved to lie in Paunescu's class; this is the conjecture that the class contains every sofic group
  commuting-sofic-actions-need-not-combine: that settles a permanence question for sofic actions on countable sets; this is the p.m.p. action question in Paunescu's crossed-product sense
---

**REFUTED.** For every sofic group `G` and every p.m.p. action `G ↷ (X,μ)` on a
standard probability space, the action is sofic in the sense of Păunescu,
Definition 1.4 (crossed product embedded in a matrix ultraproduct with the base
diagonal and the group in permutations). In the notation of Păunescu Definition
3.2: every sofic group lies in the class `𝒮`.

Asked by Păunescu, arXiv:1002.0605v5, Section 3, verbatim: *"The goal would be
to prove that every (free) action of a sofic group is sofic. While this remains
open we shall prove this fact for a family of groups."* By his Theorem 3.1 the
free and general versions are the same question for each fixed group.

**Refuter.** `kun-thom-free-nonsofic-action`: the residually finite Kazhdan
group `EL_r(F_q[x_1^(±1),...,x_d^(±1)]) ⋊ SL_d(Z)` (`r, d >= 3`) has a free
ergodic strongly ergodic nonsofic action (Kun--Thom, arXiv:2608.06222v3,
Corollary 3.2, derived from Corollary D). Kun--Thom's introduction states that
Corollary D answers Păunescu's question in the negative.

What survives. The class `𝒮` still contains every amenable group, every free
group, and is closed under amalgamation over amenable subgroups
(`paunescu-sofic-action-class-permanence`), and it is invariant under
commensurability (`sofic-action-class-closed-under-commensurability`). The
natural residual questions are recorded as `mixing-free-nonsofic-action-of-sofic-group`,
`hyperlinear-nonsofic-free-action` and `sl3z-admits-nonsofic-action`.

## Attempts

* **Positive permanence** (Păunescu Section 3): amenable groups through
  Connes--Feldman--Weiss and actions of `Z`, free groups through free products
  of sofic actions over a common amenable subgroup. This reaches treeable-type
  groups and nothing with property (T).
* **Refutation.** Property (T) plus a one-sided compression `tΓt^(-1) <= Γ`
  forces every sofic action to have a `G`-invariant `Γ`-fixed algebra
  (Kun--Thom Theorem C), which the generalized Bernoulli action over `G/Γ`
  violates. Multiplying by a Bernoulli shift makes the counterexample free.
