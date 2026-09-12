---
rg: 2
id: hyperbolic-rf-vtf-kazhdan-equivalence
kind: claim
title: Residual finiteness, virtual torsion-freeness and Kazhdan finite-quotient failures are equivalent across hyperbolic groups
distinct_from:
  hyperbolic-rf-question-equals-vtf-question: that is the two-property filling equivalence; this also supplies an infinite Kazhdan witness with no finite quotients
  hyperbolic-rf-question-equals-non-mf-question: that additionally demands the unresolved operator-MF implication; this theorem stops at the three verified group-theoretic assertions
artifacts:
  - research/artifacts/hyperbolic-four-statements-audit-2026-09-11.md
  - research/artifacts/hyperbolic-rf-vtf-osin-full-proof-2026-09-11.md
  - research/artifacts/hyperbolic-quotientless-kazhdan-proof-2026-09-11.md
---

The following statements are equivalent:

1. Some word-hyperbolic group is not residually finite.
2. Some word-hyperbolic group is not virtually torsion-free.
3. Some infinite word-hyperbolic Kazhdan group has no nontrivial finite quotient.

This is an equivalence of existence statements across the class: the witnesses
can change. It establishes none of those existence statements separately.
The proofs use Osin's Dehn filling and elementary-subgroup theorems,
Olshanskii's G-subgroup quotient theorem, and a hyperbolic Kazhdan partner.
The artifacts give the complete connective arguments and their literature
boundaries. This is a mathematical Cairn proof, not a Lean formalization.

Every non-MF word-hyperbolic group also implies these three statements,
because every countable residually finite group is operator MF. The reverse
implication to a non-MF witness is not proved by this claim. In particular,
Ozawa--Thom's obstruction to weak quasidiagonality must not be applied to raw
operator-MF approximations without an additional argument.
