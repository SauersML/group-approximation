---
rg: 2
id: free-minimal-z2-rigid-sft-via-crossing-wire-tiles
kind: route
title: The minimal crossing-wire fixed-point shift is a free minimal quantum rigid Z^2 SFT
target: free-minimal-z2-sft-is-quantum-rigid
requires:
  - minimal-crossing-wire-fixed-point-shift-is-quantum-rigid
---

Lane route (bh-g2-fixedpoint-a, 2026-09-18). Not independently reviewed.

`minimal-crossing-wire-fixed-point-shift-is-quantum-rigid` gives a `Z^2` SFT `Ω` with three properties:
- **Free.** Every period of every tiling is divisible by every `N_1 ⋯ N_k`.
- **Minimal.** This is the Durand–Romashchenko mechanism, arXiv:1802.01461 §3.2, with diversification slots
  added for crossing windows.
- **Quantum rigid.** `Ω` is `D`-quantum rigid over every field for every `D >= 1`, because every face-local edge
  family commutes.

That is the statement of the target, with `D = 1`. Equivalently, `LC(Ω, k) ⋊ Z^2` is finitely presented over
every field (`sft-crossed-product-fp-iff-quantum-rigid`).
