---
rg: 2
id: out-fn-bh-via-virtual-embedding-in-aut-fn
kind: route
title: Embed a finite-index subgroup of Out(F_n) in some Aut(F_m) and close up under finite extensions
target: out-free-groups-satisfy-boone-higman
requires:
  - out-free-groups-virtually-embed-in-aut-free-groups
  - aut-free-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

Let `n ≥ 3`.
1. By `out-free-groups-virtually-embed-in-aut-free-groups`, a finite-index
   `L ≤ Out(F_n)` embeds in some `Aut(F_m)`.
2. `Aut(F_m)` satisfies the permutational Boone--Higman conjecture by BFFHZ
   Theorem A (`aut-free-groups-satisfy-permutational-boone-higman`), i.e. it
   lies in the class `B_A`.
3. `B_A` is closed under subgroups and finite-index overgroups
   (`boone-higman-type-a-class-closed-under-finite-extensions`). So first `L`,
   then `Out(F_n)`, lies in `B_A`.
4. Every member of `B_A` embeds in a finitely presented simple group, by part 3
   of that claim.
