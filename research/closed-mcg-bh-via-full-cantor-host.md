---
rg: 2
id: closed-mcg-bh-via-full-cantor-host
kind: route
title: Closed-surface mapping class groups satisfy Boone--Higman if a finite-index subgroup embeds in a finitely presented full clopen-transitive Cantor group
target: closed-surface-mapping-class-groups-satisfy-boone-higman
requires:
  - closed-mcg-virtually-embeds-in-fp-full-cantor-group
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
  - boone-higman-type-a-class-closed-under-finite-extensions
---

Let `g ≥ 3`.
1. By `closed-mcg-virtually-embeds-in-fp-full-cantor-group`, a finite-index
   subgroup `L ≤ Mod(Σ)` embeds in a finitely presented, full, clopen-transitive
   group `D` of Cantor homeomorphisms.
2. `D` acts with type (A) on its proper nonempty clopen sets
   (`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`). So `D`, and
   with it `L`, lies in the permutational Boone--Higman class `B_A`, which is
   closed under subgroups.
3. `B_A` is closed under finite-index overgroups, and each of its members embeds
   in a finitely presented simple group (items 2 and 3 of
   `boone-higman-type-a-class-closed-under-finite-extensions`). So `Mod(Σ)`
   embeds in a finitely presented simple group.

The route inherits the review status of step 2: that node is a lane proof, not
independently reviewed. The Brin--Thompson instance `D = nV`, `n ≥ 2`, is recorded
on the premise. It is not excluded by any node on main, because the obstruction
for `V` does not transfer to `2V`.
