---
rg: 2
id: closed-mcg-bh-via-aut-free-host
kind: route
title: Closed-surface mapping class groups satisfy Boone--Higman if they embed in some Aut(F_n)
target: closed-surface-mapping-class-groups-satisfy-boone-higman
requires:
  - every-closed-surface-mcg-embeds-in-some-aut-free-group
  - aut-free-groups-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Let `g ≥ 3`.
1. By `every-closed-surface-mcg-embeds-in-some-aut-free-group`, `MCG(S_g)` embeds
   in some `Aut(F_n)`.
2. `Aut(F_n)` lies in the permutational Boone--Higman class `B_A` by BFFHZ
   Theorem A (`aut-free-groups-satisfy-permutational-boone-higman`), the same input
   as step 2 of `out-fn-bh-via-virtual-embedding-in-aut-fn`.
3. `B_A` is closed under subgroups, and every member embeds in a finitely presented
   simple group (items 1 and 3 of
   `boone-higman-type-a-class-closed-under-finite-extensions`).

This premise is weaker than the one in `closed-mcg-bh-via-punctured-mcg-host`,
which implies it (`closed-mcg-aut-embedding-via-punctured-host`): any faithful
action of a finite-index subgroup on a finitely generated free group suffices.
