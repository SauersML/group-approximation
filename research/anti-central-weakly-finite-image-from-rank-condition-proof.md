---
rg: 2
id: anti-central-weakly-finite-image-from-rank-condition-proof
kind: route
title: The general weakly finite image theorem applied to the anti-central summand, with the unit group embedded by simplicity
target: anti-central-rank-condition-gives-weakly-finite-image
requires: [rank-condition-rings-have-weakly-finite-images, anti-central-state-obstruction-equals-stable-finiteness, odd-leavitt-unit-groups-mod-scalars-are-fp-simple, leavitt-gl-equals-el-and-perfect-unit-group]
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

Artifact Corollary C.2.
1. A state on `(K_0(S_-), [eps_-])` means no multiple of `[eps_-]` is `<= 0` (part 2 of
   `anti-central-state-obstruction-equals-stable-finiteness`). That is the rank condition for `S_-`.
2. `rank-condition-rings-have-weakly-finite-images` gives a maximal `J`, with `W = S_- / J` weakly finite,
   nonzero, and with all states faithful on idempotent matrices.
3. **The embedding.** The kernel of `G_3 -> W^x`, `g -> [g] eps_- + J`, is normal.
   - It misses `z`: `1 - z` maps to `2·1_W != 0` in the nonzero `F_3`-algebra `W`.
   - A normal subgroup missing `z` meets `<z>` trivially, and maps to `1` or `PG` in the simple group `PG`.
   - The image `PG` would split off `<z>` and contradict perfection. So the kernel is trivial.
