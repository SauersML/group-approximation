---
rg: 2
id: char-p-transcendental-gl-n-avoids-v-and-va-for-n-ge-3
kind: claim
title: If K has characteristic p and is not algebraic over F_p, then for n >= 3 GL_n(K) embeds in neither V nor VA
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that root's obstruction O2 excludes V and VA for GL_n(Q), n >= 3, through SL_3(Z); this is the characteristic-p analogue, through the Kazhdan group SL_3(F_p[t]).
  char-p-linear-groups-have-no-distorted-cyclic-subgroups: that shows the distortion obstruction never applies in characteristic p; this shows that property (T) still excludes V and VA in characteristic p once n >= 3, leaving n = 2 open.
---

**ESTABLISHED** by `char-p-transcendental-gl-n-avoids-v-and-va-proof`
(classical inputs cited without re-reading at the source; lane-proved, not
independently reviewed; no priority claimed).

## Statement

Let `K` be a field of characteristic `p` containing an element `t` transcendental
over `F_p`, for example `K = F_q(t)`, and let `n >= 3`. Then `GL_n(K)` embeds in
neither Thompson's group `V` nor Belk--Hyde--Matucci's group `VA`, nor in any
subgroup of them.

## What is left

For `n = 2` neither this nor the distortion obstruction applies
(`char-p-linear-groups-have-no-distorted-cyclic-subgroups`). So `V` and `VA`
are still candidate hosts for `GL_2(F_q(t))`, whereas `GL_2(Q)` is excluded
from `VA` by distortion (O4 of `gl-n-q-embeds-in-fp-simple-group`).

DERIVATION
char-p-transcendental-gl-n-avoids-v-and-va-proof
