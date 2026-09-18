---
rg: 2
id: bs13-embeds-in-brin-thompson-3v
kind: claim
title: The Baumslag-Solitar group BS(1,3) embeds in the Brin-Thompson group 3V
distinct_from:
  bs12-embeds-in-brin-thompson-2v: that asks for BS(1,2) (an element conjugate to its square) in some nV; this is BS(1,3) in 3V.
  bs-1-n-does-not-embed-in-thompson-v: that excludes every BS(1,n), n >= 2, from V; this puts BS(1,3) in 3V.
  renormalizable-thompson-elements-give-baumslag-solitar: that is the general criterion; this is its first instance.
---

**OPEN.** There are `s, u ∈ 3V` with `s` of infinite order and `u s u^-1 = s^3`, so
`BS(1,3) = ⟨a, t | t a t^-1 = a^3⟩ ≅ ⟨s, u⟩ ≤ 3V`.

**Status.** Route `bs13-in-3v-via-smart-renormalization` reduces it to
`smart-induced-map-has-brick-local-height-3-renormalization`, which is under review (proof claimed
2026-09-18).

**What it would give.**
- An element of `3V` with logarithmic distortion, `|s^{3^n}| = O(n)`. The Callard–Salo element has
  `O(log^4 N)`.
- The Baumslag–Solitar gate of `rational-stepping-stones-in-nv-need-bs12-or-heisenberg` is passable
  for the prime 3. The gate for 2, which `GL_2(Q)` and `Aff(Q)` need, stays open.
- It contradicts the Baumslag–Solitar exclusions of Sheng arXiv:2209.11982 for `nV`, which were
  withdrawn in v2.
