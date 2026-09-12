---
rg: 2
id: bernoulli-shifts-with-equal-base-entropy-are-isomorphic
kind: claim
title: Bernoulli shifts whose bases have equal Shannon entropy are isomorphic over every countably infinite group
distinct_from:
  bernoulli-shift-entropy-classifies-for-every-group: that is the open converse, that different base entropies give non-isomorphic shifts; this is the established half, that equal base entropies give isomorphic shifts.
---

**ESTABLISHED (import).** Let `G` be a countably infinite group, and let
`(L,lambda)` and `(K,kappa)` be standard probability spaces with
`H(L,lambda) = H(K,kappa)`. Then the Bernoulli shifts `G ↷ (L^G,lambda^G)` and
`G ↷ (K^G,kappa^G)` are isomorphic. When `L` and `K` are finite, the isomorphism
can be taken finitary.

So the isomorphism class of a Bernoulli shift over `G` depends only on the
Shannon entropy of its base.

**Source.** B. Seward, *Bernoulli shifts with bases of equal entropy are
isomorphic*, arXiv:1805.08279v1. Read on 2026-09-12 from the PDF text extracted
on MSI (`review-lit/entropy/1805.08279.txt`). Verbatim, Theorem 1.1: "Let G be a
countably infinite group and let (L,λ) and (K,κ) be standard probability spaces.
If H(L,λ) = H(K,κ) then the Bernoulli shifts G y (L^G,λ^G) and G y (K^G,κ^G) are
isomorphic." Theorem 1.3 is the finitary version for finite `L` and `K`.

History, from the same introduction:
- Ornstein proved the case `G = Z`.
- Ornstein and Weiss proved it for amenable groups.
- Stepin observed that the property passes to supergroups.
- Bowen proved it in 2011 when both supports have at least 3 points.
