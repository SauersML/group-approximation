---
rg: 2
id: boone-higman-via-rover-nekrashevych-hosts
kind: route
title: Dead - embed the input in a finitely presented simple Rover--Nekrashevych commutator host
target: boone-higman-conjecture
requires:
  - decidable-groups-embed-in-rover-nekrashevych-hosts
---

**Dead.** Invalidated by `deligne-lattice-embeds-in-no-rover-nekrashevych-group`,
and its premise is refuted. Kazhdan subgroups of `V_d(H)` are residually finite
(`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`), and Deligne's lattice
is a decidable Kazhdan group that is not.

The composition itself would be immediate. The premise embeds the input `G` in `[V_d(H),V_d(H)]` and makes that
host finitely presented and simple.

The route is kept separate from the premise so that the host shape the
self-similar method must use for the general conjecture stays visible. Self-similar
hosts are excluded by `self-similar-hosts-contain-only-residually-finite-groups`.
