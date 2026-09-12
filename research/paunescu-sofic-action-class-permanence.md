---
rg: 2
id: paunescu-sofic-action-class-permanence
kind: claim
title: Paunescu's class of groups all of whose p.m.p. actions are sofic contains amenable and free groups and is closed under amalgamation over amenable subgroups
distinct_from:
  gkp-sofic-action-toolkit: that is permanence for sofic actions on countable SETS (Gao--Kunnawalkam Elayavalli--Patchell); this is permanence for p.m.p. actions on probability spaces in Paunescu's crossed-product sense, a different notion
  kun-thom-free-nonsofic-action: that is the counterexample showing a sofic group outside the class; this records the positive facts proved about the class
artifacts:
  - research/artifacts/free-nonsofic-action-sources-verified-2026-09-11.md
---

**ESTABLISHED (literature import).** L. Păunescu, *On sofic actions and
equivalence relations*, arXiv:1002.0605v5, J. Funct. Anal. 261 (2011), verbatim
from the v5 PDF (artifact). A p.m.p. action is *sofic* when (Definition 1.4)
`L^∞(X) ⋊_α G` embeds in `Π_(k→ω) M_(n_k)(C)` with `L^∞(X)` in the diagonal and
`G` in the permutation matrices; it is *hyperlinear* when (Definition 1.3) the
crossed product embeds in `R^ω`.

> **Definition 3.2.** Denote by 𝒮 the class of groups for which every action
> is sofic.

The facts imported:

1. **Free actions suffice** (Theorem 3.1): *"Let G be a group such that every
   free action is sofic. Then every action of G is sofic."* (Product with a free
   action and restrict the embedding.)
2. **Amenable groups** (Proposition 3.4): *"Amenable groups are in 𝒮."*
3. **Free groups** (Corollary 3.7): *"Each action of a free group, including
   𝔽_∞ is sofic."*
4. **Amalgamation** (Theorem 3.9): *"Class 𝒮 is closed under amalgamated
   product over amenable groups. It is strictly larger than the class of
   treeable groups."* The strictness witness is `Z *_((2,3)Z) Z`.
5. **Orbit relations** (Proposition 1.15): *"Let α be a free action. Then E_α
   is a sofic equivalence relation if and only if α is a sofic action."*

What the paper leaves open, verbatim from the start of its Section 3: *"The goal
would be to prove that every (free) action of a sofic group is sofic. While this
remains open we shall prove this fact for a family of groups."* That goal is
`sofic-groups-in-paunescu-sofic-action-class`, refuted by
`kun-thom-free-nonsofic-action`.

Further permanence proved in this graph: `sofic-action-class-closed-under-commensurability`.

**Trust surface.** Refereed; verbatim from the arXiv v5 PDF; not formalised.
