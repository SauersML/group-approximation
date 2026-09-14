---
rg: 2
id: stable-ac-conjecture-via-one-stabilization
kind: route
title: One-stabilization AC-triviality implies the stable Andrews–Curtis conjecture
target: stable-andrews-curtis-conjecture
requires:
  - balanced-trivial-presentations-one-stabilization-ac-trivial
---

Let S = ⟨y_1, …, y_m | s_1, …, s_m⟩ present the trivial group.
1. One (AC4) move gives ⟨y_1, …, y_m, x | s_1, …, s_m, x⟩. Swapping relators is an AC
   composite (see `shehper-z-conjecture-one-stabilization-proof`, (E2)), so this is
   AC-equivalent to the premise's form ⟨x, y | x, s⟩.
2. By the premise it is AC-trivial.
3. m+1 applications of (AC5) remove the trivial relators.

So S is stably AC-trivial.
