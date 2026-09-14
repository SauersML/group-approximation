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

## Review
- **sk-verify-19 PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-19-2026-09-14-part2.md` §3):** ⇐ is Theorem 1. For ⇒:
  - the quotient V_n/A is a sofic approximation of Γ with limit Q^A (A acts almost freely; lifts of g ≠ 1 move most A-orbits);
  - Gohla–Thom Theorem 3.4, stability, and Lemma 2.13/Cor 2.14 in the import's direction give inf_X |||θ^X(α)||| = 0.
  - Fixes: (F1) the comparability |||θ^X(α)||| ~ ν_X(α) appeals to Gohla–Thom §2.2, which is not in the import node. Add it to the citation import, or fix the presentation-complex model with uniform weights, where equality holds by definition. (F2) State the one-line reason that V_n/A is a sofic approximation of Γ with limit P = Q^A.
