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

**Relation to `every-group-has-positive-rokhlin-entropy-action`.** Under that
hypothesis Seward's Krieger II (arXiv:1501.03367) gives Bernoulli Rokhlin
entropy equal to base entropy. Rokhlin entropy is an isomorphism invariant, so
the hypothesis implies this claim. The route stays unwired until the per-group
form is read.

## Attempts

- None run. The strategy lane `opportunity-mapper` opened this claim; see item
  2 of `research/artifacts/opportunity-map-2026-09-12.md`.
- Weak isomorphism gives no obstruction. Every nonsofic group known here
  contains a nonabelian free subgroup, and over such groups every pair of
  nontrivial Bernoulli shifts is weakly isomorphic (Bowen, arXiv:0812.2718). A
  counterexample needs an actual isomorphism that changes base entropy.
