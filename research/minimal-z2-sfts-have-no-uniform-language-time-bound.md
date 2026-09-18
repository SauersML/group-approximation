---
rg: 2
id: minimal-z2-sfts-have-no-uniform-language-time-bound
kind: claim
title: For every recursive time bound there is a minimal Z^2-SFT whose pattern language is not decidable within it
distinct_from:
  complexity-bounded-host-classes-are-not-universal: that says a universal host class cannot share one word-problem bound; this shows that the dynamical supply of hard minimal Z^2-SFTs, which such a class would need over Z^2, is not exhausted by any recursive bound.
  free-minimal-z2-sft-is-quantum-rigid: that asks for quantum rigidity of one free minimal Z^2-SFT; this concerns only language complexity and says nothing about freeness or rigidity.
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

**ESTABLISHED (unreviewed; imports Durand–Romashchenko arXiv:1802.01461
verbatim).** Let `T : N -> N` be recursive. Then there is a minimal `Z^2`-SFT
`X` such that, for no constant `C`, is the set of globally admissible `n × n`
patterns of `X` decidable in time `C·T(Cn) + Cn^2 + C`.

Every minimal SFT has a decidable language. So this is exactly the answer "no"
to the w4 need 1fcab928: is the language complexity of minimal `Z^2`-SFTs
uniformly bounded?

**Why it matters.** Attempt 6 of
`decidable-group-algebras-have-fp-cantor-crossed-hosts` isolates a
symbolic-dynamics prerequisite. Viable hosts need minimal SFTs with no uniform
recursive language bound, and for free groups this fails outright. Over `Z^2`,
and hence over `Z^2 × F_d` by
`cantor-crossed-hosts-are-closed-under-boundary-products`, the language part
holds. What is still open is getting it together with freeness and quantum
rigidity.

**Caveat.** The SFT produced need not be free: its trivially acting subgroup is
contained in `0 × Z`, but can be nontrivial. Its quantum rigidity is unknown.

DERIVATION
minimal-z2-sfts-have-no-uniform-language-time-bound-proof
