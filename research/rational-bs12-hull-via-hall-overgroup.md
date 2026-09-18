---
rg: 2
id: rational-bs12-hull-via-hall-overgroup
kind: route
title: If the Hall-type overgroup of Q x|_2 Z lies in B_A, so does Q x|_2 Z, because B_A is closed under subgroups
target: rational-bs12-hull-in-permutational-bh-class
requires:
  - rational-bs12-hull-embeds-in-a-fg-solvable-group
  - rational-bs12-hall-overgroup-in-permutational-bh-class
  - boone-higman-type-a-class-closed-under-finite-extensions
---

- By `rational-bs12-hull-embeds-in-a-fg-solvable-group`, `D_2 = Q x|_2 Z` embeds
  in `Ĥ`.
- By `rational-bs12-hall-overgroup-in-permutational-bh-class`, `Ĥ ∈ B_A`.
- `B_A` is closed under subgroups: item 1 of
  `boone-higman-type-a-class-closed-under-finite-extensions`. Explicitly, `D_2`
  embeds in whatever finitely presented type (A) actor contains `Ĥ`.
- Hence `D_2 ∈ B_A`.
