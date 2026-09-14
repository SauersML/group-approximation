---
rg: 2
id: dual-surjunctive-surjunctive-via-post-surjective-decoders
kind: route
title: Choose a post-surjective decoder for a strict pair and read it as a dual-surjunctivity failure
target: dual-surjunctive-groups-are-surjunctive
requires:
  - strict-pairs-admit-post-surjective-decoders
  - post-surjective-decoders-convert-strict-pairs-to-dual-failures
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

Let `G` be dual surjunctive and suppose `G` is not surjunctive.
1. `G` carries a strict pair.
2. By `strict-pairs-admit-post-surjective-decoders`, it carries a strict pair
   `(τ, σ)` with `σ` post-surjective.
3. By (a) of the conversion claim, `σ` is post-surjective and not
   pre-injective. That contradicts dual surjunctivity.
