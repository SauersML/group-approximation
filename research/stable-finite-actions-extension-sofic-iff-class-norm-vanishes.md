---
rg: 2
id: stable-finite-actions-extension-sofic-iff-class-norm-vanishes
kind: claim
title: Over a finitely presented residually finite base stable in finite actions, a finite central extension is sofic exactly when its class has vanishing finite-action Hamming norm
distinct_from:
  gohla-thom-stable-base-nonsofic-extension: that is Gohla--Thom Theorem 3.13, the nonsofic direction under a uniform cosystolic inequality; this is the two-sided criterion under stability alone, with the sofic direction supplied by finite-action torsors.
  finite-actions-with-vanishing-class-norm-make-extension-sofic: that is the unconditional sofic direction; this adds the converse for stable bases.
artifacts:
  - research/artifacts/sk-deligne-sofic-2026-09-14-part1.md
---

**ESTABLISHED** (`stable-finite-actions-extension-sofic-iff-norm-proof`). Unreviewed.

Let `Gamma` be finitely presented, residually finite, and stable in finite actions (Gohla--Thom arXiv:2403.09582,
Definition 3.7). Let `A` be finite abelian and `alpha` the class of `Gamma~`. Then `Gamma~` is sofic iff
`inf_X nu_X(alpha) = 0` over finite `Gamma`-sets `X`, with `nu_X` as in
`finite-actions-with-vanishing-class-norm-make-extension-sofic`.

Consequence: over such a base, a non-residually-finite `Gamma~` is either sofic or supports a uniform positive Hamming
lower bound for its class on all finite actions. Gohla--Thom Theorem 3.13 is the second alternative forced by a
cosystolic inequality.
