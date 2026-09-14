---
rg: 2
id: balanced-trivial-presentations-one-stabilization-ac-trivial
kind: claim
title: Every balanced presentation of the trivial group becomes Andrews–Curtis trivial after one stabilization
distinct_from:
  andrews-curtis-conjecture: that asks for AC-triviality with no stabilization; this allows exactly one added generator with its trivial relator
  stable-andrews-curtis-conjecture: that allows any number of stabilizations and destabilizations interleaved with AC moves; this allows a single stabilization at the start
artifacts:
  - research/artifacts/hl-andrews-curtis-status-2026-09-13.md
---

**OPEN.** For every balanced presentation ⟨y_1, …, y_m | s_1, …, s_m⟩ of the trivial
group, ⟨x, y_1, …, y_m | x, s_1, …, s_m⟩ is AC-trivial.

- **Implied by** `andrews-curtis-conjecture`, through the route
  `one-stabilization-ac-via-andrews-curtis`.
- **Implies:**
  - `stable-andrews-curtis-conjecture`;
  - `ak3-is-stably-ac-trivial`;
  - through `shehper-z-conjecture-iff-one-stabilization-ac`, Shehper et al.'s
    `shehper-z-presentations-are-ac-trivial`.
- **Rank m case:** it is exactly that conjecture on m+1 generators.
