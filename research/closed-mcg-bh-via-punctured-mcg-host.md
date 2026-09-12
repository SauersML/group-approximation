---
rg: 2
id: closed-mcg-bh-via-punctured-mcg-host
kind: route
title: Embed a finite-index subgroup in a punctured-surface mapping class group and close up under finite extensions
target: closed-surface-mapping-class-groups-satisfy-boone-higman
requires:
  - closed-mcgs-virtually-embed-in-punctured-mcgs
  - punctured-surface-mcgs-satisfy-permutational-boone-higman
  - boone-higman-type-a-class-closed-under-finite-extensions
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

Let `Σ` be closed of genus `g ≥ 3`.
1. By `closed-mcgs-virtually-embed-in-punctured-mcgs`, a finite-index
   `L ≤ Mod(Σ)` embeds in the extended mapping class group of a surface `Σ′`
   with a puncture or boundary component.
2. That group lies in the class `B_A` by
   `punctured-surface-mcgs-satisfy-permutational-boone-higman`.
3. `B_A` is closed under subgroups and finite-index overgroups
   (`boone-higman-type-a-class-closed-under-finite-extensions`). So first `L`,
   then `Mod(Σ)`, lies in `B_A`.
4. By part 3 of the same claim, every member of `B_A` embeds in a finitely
   presented simple group.
