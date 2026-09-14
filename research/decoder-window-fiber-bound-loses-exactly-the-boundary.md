---
rg: 2
id: decoder-window-fiber-bound-loses-exactly-the-boundary
kind: claim
title: The decoder of an injective automaton bounds window fibers above the average by exactly the boundary patterns
distinct_from:
  window-balance-is-a-fiber-upper-bound: that is the exact one-sided form of balance for any automaton; this is the upper bound that injectivity actually supplies, which misses that form by the factor q^|d_N E|.
  every-injective-ca-preserves-uniform-bernoulli-measure: that is the open universal preservation statement; this is a proved per-window inequality with an explicit loss, which proves preservation only when the loss has zero density, as on amenable groups.
artifacts:
  - research/artifacts/window-balance-mass-transport-2026-09-12.md
---

**ESTABLISHED** (artifact Section 3, route `decoder-window-fiber-bound-proof`).

Let `tau` on `A^G` be injective with memory `M` and decoder memory `N` containing `1`, so
`x(g) = nu((tau(x)(gn))_(n in N))`. For a finite window `E` put `int_N E = {g : gN is contained in E}`
and `d_N E = E \ int_N E`. Then for every `p in A^E`

    c_E(p) <= q^(|EM| - |int_N E|) = q^(|EM| - |E|) * q^(|d_N E|) .

Against `window-balance-is-a-fiber-upper-bound`, the loss is exactly `q^(|d_N E|)`.

**What it proves and where it stops.**
- On amenable groups, Folner windows make `|d_N F| / |F| -> 0`. Counting patterns that avoid
  disjoint translates of a Garden of Eden then contradicts the bound, which is Gromov--Weiss
  surjunctivity in fiber-count form.
- On nonamenable groups the boundary density is bounded below. The per-window inequality is
  consistent once the Garden of Eden is large, and averaging over translates or invariant random
  windows does not change the density.
- At the single window `E = {1}` with `|N| >= 2`, `int_N E` is empty, so the bound is vacuous. The
  one-site equation, which carries the whole problem, gets nothing from the decoder at scale one.
