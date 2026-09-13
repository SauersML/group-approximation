---
rg: 2
id: kun-thom-wreath-maximality-from-amenable-kernel-ascent
kind: route
title: Ascend Rokhlin maximality from the residually finite actor across the locally finite lamp kernel
target: kun-thom-wreath-bernoulli-rokhlin-maximal
requires: [rokhlin-maximality-ascends-amenable-normal-extensions, kun-thom-nonsofic-wreath]
---

- **Setup.** `W = (Z/2)^(G/Γ) ⋊ G`, with the lamp group `N = (Z/2)^(G/Γ)` normal, locally finite and hence
  amenable, and `W/N ≅ G`.
- **The quotient is maximal.** `G` is residually finite by Theorem E (`kun-thom-nonsofic-wreath`), hence
  sofic. By the sofic case recorded in `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, its uniform
  Bernoulli shifts have Rokhlin entropy `k log q` for every `k` and `q`.
- **Ascent.** `rokhlin-maximality-ascends-amenable-normal-extensions` then gives maximality of `W` at every `q`.

This route fires only if the ascent claim is established. The ascent is open.
