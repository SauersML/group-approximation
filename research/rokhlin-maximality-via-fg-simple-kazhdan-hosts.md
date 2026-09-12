---
rg: 2
id: rokhlin-maximality-via-fg-simple-kazhdan-hosts
kind: route
title: Prove maximal Bernoulli Rokhlin entropy on simple Kazhdan hosts and restrict to subgroups
target: bernoulli-rokhlin-entropy-maximal-for-every-group
requires: [bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups, countable-group-embeds-in-fg-simple-kazhdan-group, bernoulli-rokhlin-maximality-passes-to-subgroups]
artifacts:
  - research/artifacts/bernoulli-deficit-witness-localization-2026-09-12.md
---

Let `C` be a countably infinite group and `A` a finite alphabet.
1. The second prerequisite embeds `C` in a finitely generated infinite simple Kazhdan group `G`.
2. By the first prerequisite, `G` is Rokhlin-maximal at `|A|` for every amplification `A^k`.
3. Part 1 of the third prerequisite passes maximality to `C`.

This is Proposition 5 of the artifact.

The converse is specialization. Like `gottschalk-via-fg-simple-kazhdan-hosts`, this route therefore
pairs an exact reduction with a hole equivalent to its target.
