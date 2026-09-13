---
rg: 2
id: split-quotient-euler-obstruction-to-bnsr-invariants-proof
kind: route
title: Meinert's split-epimorphism corollary transfers membership to the quotient, whose top invariant is empty
target: split-quotient-euler-obstruction-to-bnsr-invariants
requires:
  - euler-characteristic-empties-top-bnsr-invariant
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-top-range-2026-09-13.md
---

Meinert, 1997, Corollary 2.8, as quoted by Zaremsky (arXiv:1507.08597v1,
Citation 1.3): "Let `G -> Q` be a split epimorphism of groups. Let
`chi: Q -> R` be a character. Let `chi~ = chi o pi`. If `[chi~] in Sigma^m(G)`
then `[chi] in Sigma^m(Q)`."

So `[psi o pi] in Sigma^d(G)` would give `[psi] in Sigma^d(Q)`. But
`Sigma^d(Q) <= Sigma^d(Q; Z)`, which is empty by
`euler-characteristic-empties-top-bnsr-invariant`, since `Q` has a finite
`d`-dimensional classifying space and `chi(Q) != 0`. Artifact, Section 4.
