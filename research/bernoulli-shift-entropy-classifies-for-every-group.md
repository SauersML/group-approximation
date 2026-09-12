---
rg: 2
id: bernoulli-shift-entropy-classifies-for-every-group
kind: claim
title: Bernoulli shifts with different base entropy are non-isomorphic over every countably infinite group
root: true
distinct_from:
  coset-bernoulli-action-is-essentially-free: that is freeness of one generalized Bernoulli action over a coset space; this is the isomorphism classification of ordinary Bernoulli shifts by base entropy, over all groups.
---

**OPEN.** Let `G` be a countably infinite group, and let `(L,λ)` and `(K,κ)`
be standard probability spaces with `H(L,λ) ≠ H(K,κ)`. Then the Bernoulli
shifts `G ↷ (L^G,λ^G)` and `G ↷ (K^G,κ^G)` are not isomorphic.

**Source.** B. Seward, *Bernoulli shifts with bases of equal entropy are
isomorphic*, arXiv:1805.08279 (J. Mod. Dyn. 2022). From the introduction, read
from the arXiv HTML on 2026-09-12:
- "As entropy is an isomorphism invariant, it follows that G↷(L^G,λ^G) and
  G↷(K^G,κ^G) are non-isomorphic whenever G is sofic (so the sofic entropy is
  defined) and H(L,λ)≠H(K,κ)."
- "If non-sofic countable groups G exist, then it is still unknown whether
  (2^G,u_2^G) and (3^G,u_3^G) are isomorphic."

The same paper proves that equal base entropy gives isomorphic Bernoulli shifts
over every countably infinite group, so this claim is exactly the missing half
of the classification. It holds for sofic groups, so a counterexample must be
nonsofic. Nonsofic groups now exist (`openai-leavitt-unit-nonsofic`).

**Relation to `every-group-has-positive-rokhlin-entropy-action`.** The route
`bernoulli-classification-via-positive-rokhlin-entropy` derives this claim from
that hypothesis and `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`:
- INF(G) follows for each group through products `P × G`, by Seward Theorem 1.11;
- INF(G) then gives Bernoulli Rokhlin entropy equal to base entropy;
- Rokhlin entropy is an isomorphism invariant.

Per group, the scope is narrower:
- INF(G) alone gives this claim for `G`;
- for one pair of finite base entropies `h_1 < h_2`, the weaker bound
  `h^Rok_sup(G) > h_1` suffices.

Necessary conditions on a counterexample group are recorded in
`bernoulli-entropy-counterexample-constraints`.

## Attempts

- **Origin and wiring.** The strategy lane `opportunity-mapper` opened this
  claim (item 2 of `research/artifacts/opportunity-map-2026-09-12.md`). Lane
  `bernoulli-entropy-classification` read the per-group statements of Seward
  II, wrote the route above and the counterexample constraints, and was merged
  into lane `rokhlin-entropy` on 2026-09-12.
- **No lower bound.** Every lower bound for Rokhlin entropy used here comes
  from sofic entropy or amenability. The attempts toward one without sofic
  models are recorded on `every-group-has-positive-rokhlin-entropy-action`.
- Weak isomorphism gives no obstruction. Every nonsofic group known here
  contains a nonabelian free subgroup, and over such groups every pair of
  nontrivial Bernoulli shifts is weakly isomorphic (Bowen, arXiv:0812.2718). A
  counterexample needs an actual isomorphism that changes base entropy.
