---
rg: 2
id: sofic-free-actions-are-soe-invariant
kind: claim
title: Soficity of free p.m.p. actions is invariant under stable orbit equivalence
distinct_from:
  cordeiro-sofic-relation-permanence: that imports restriction of sofic relations to subsets; this adds the converse, amplification from a subset meeting almost every class, and the resulting invariance for free actions of different groups
  paunescu-sofic-action-class-permanence: that imports Paunescu's Proposition 1.15 for one free action and its own orbit relation; this transports soficity between free actions whose orbit relations are only stably isomorphic
artifacts:
  - research/artifacts/paunescu-class-measure-equivalence-2026-09-12.md
---

**ESTABLISHED.**

1. **Amplification.** Let `R` be a p.m.p. countable Borel equivalence relation on
   a finite measure space `(W, m)`, and `V ⊆ W` a non-null Borel set meeting almost
   every `R`-class. If `R|_V` is sofic, then `R` is sofic. With Cordeiro's
   Proposition 3.2(a) the converse also holds.
2. **SOE invariance.** Let `a : G ↷ (X, μ)` and `b : H ↷ (Y, ν)` be essentially
   free p.m.p. actions of countable groups, and suppose non-null sets `A ⊆ X`,
   `B ⊆ Y` meeting almost every orbit carry isomorphic restricted orbit relations
   (up to scaling the measure). Then `a` is sofic (Păunescu Definition 1.4) iff `b`
   is sofic.
3. The same holds with "sofic" replaced by "the crossed product embeds in `R^ω`".

Soficity of a free action is therefore a property of the stable orbit equivalence
class of its orbit relation. The group, the action and the dynamics (mixing,
ergodic structure of subgroups) can change inside that class.

Proof in `sofic-free-actions-are-soe-invariant-proof` (Section 2 of the artifact).
