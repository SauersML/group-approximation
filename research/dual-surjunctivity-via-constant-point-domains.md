---
rg: 2
id: dual-surjunctivity-via-constant-point-domains
kind: route
title: Restrict a would-be dual failure to the SFT avoiding one padded collision pattern and forbid strongly post-surjective covers of constant-point domains
target: every-group-is-dual-surjunctive
requires:
  - dual-failures-give-constant-point-cover-pairs
  - constant-point-sft-domains-admit-no-post-surjective-covers
artifacts:
  - research/artifacts/erasable-pattern-avoiding-cover-pairs-2026-09-19.md
---

Suppose `F : A^G → A^G` is post-surjective and not pre-injective. By
`dual-failures-give-constant-point-cover-pairs`, there is a proper SFT `X ⊊ A^G` containing every constant such
that `F|_X : X → A^G` is strongly post-surjective with lifts in `X`. This contradicts
`constant-point-sft-domains-admit-no-post-surjective-covers` at `G`. So every post-surjective automaton over `G`
is pre-injective.

The route works group by group: CP(G) ⇒ DualSurj(G). It runs parallel to `gottschalk-via-constant-point-domains`,
so the single open input CP feeds both `gottschalk-surjunctivity-conjecture` and this target.
