---
rg: 2
id: some-group-has-isomorphic-bernoulli-shifts-of-different-entropy
kind: claim
title: Some countably infinite group has isomorphic Bernoulli shifts whose bases have different Shannon entropy
distinct_from:
  bernoulli-shift-entropy-classifies-for-every-group: that is the universal classification; this is its negation, the existence of one group where it fails.
  bernoulli-isomorphism-collapse-set-is-a-subgroup: that proves the structure of the collapse subgroup D(G) on every group; this asks that D(G) be nonzero for one group.
---

**OPEN.** There is a countably infinite group `G` and standard probability spaces `(L, lambda)`, `(K, kappa)`
with `H(L, lambda) != H(K, kappa)` such that `G ↷ (L^G, lambda^G)` and `G ↷ (K^G, kappa^G)` are isomorphic.
Equivalently, `D(G) != {0}` in `bernoulli-isomorphism-collapse-set-is-a-subgroup`.

It is the negation of `bernoulli-shift-entropy-classifies-for-every-group`. Seward, arXiv:1805.08279v1,
introduction: "if non-soﬁc countable groups G exist, then it is still unknown whether (2^G,u_2^G) and
(3^G,u_3^G) are isomorphic."

Necessary conditions on `G` are in `bernoulli-entropy-counterexample-constraints`: nonsofic, small Rokhlin
supremum, and failure passes to supergroups.

Routes into this claim:
- `leavitt-induced-absorption-gives-bernoulli-collapse`, from
  `leavitt-unit-algebra-absorbs-an-induced-projective` through
  `induced-projective-absorption-breaks-bernoulli-classification`.
