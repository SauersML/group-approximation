---
rg: 2
id: odometer-factor-witnesses-mix-coordinates
kind: claim
title: An element of kV with an infinite odometer factor has no power in any conjugate of the triangular subgroup, so k >= 2 and it must mix coordinates
distinct_from:
  some-brin-thompson-element-factors-onto-an-odometer: that is the open existence question; this lists established necessary conditions on a witness.
  renormalizable-thompson-elements-are-odometer-codes: that derives the odometer factor, no periodic points and zero drift from a renormalization; this starts from the factor alone.
  triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z: that proves periodic points for triangular elements; this applies it to odometer factors.
---

**ESTABLISHED (2026-09-17)** through `odometer-factor-witnesses-mix-coordinates-proof`.
Lane proof (gq-nv-obstruct). Not independently reviewed.

**Statement.** Let `k >= 1`, `m >= 2`, and `T ∈ kV` with a continuous
surjection `π: C^k -> Z_m` such that `π ∘ T = π + 1`. Then:
1. For every `r >= 1`, `T^r` has no periodic point.
2. No `T^r`, `r >= 1`, lies in `f σ T_k σ^-1 f^-1` for any `f ∈ kV` and any
   coordinate permutation `σ`. Here `T_k` is the triangular subgroup of
   `triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z`, which contains
   `V^k`.
3. In particular `k >= 2`: no element of Thompson's group `V` (where `T_1 = V`)
   factors onto an infinite odometer. For `k >= 2`, no power of a witness lies
   in any conjugate of `V^k`, or of a group `C(C, V) ⋊ V`-type iterated cocycle
   group. A witness has to move material between coordinates, as the baker's
   map and SMART-type machines do.
4. No power of a witness is conjugate to an element of the topological full
   group of the full shift embedded in `kV` by coding, because those elements fix
   the constant configurations (item 1).

**Consequence for the search.** Together with item 4 of
`renormalizable-thompson-elements-are-odometer-codes`, the candidates are
non-triangular in every coordinate order and every conjugate, for every power.
The known periodic-point-free elements of `2V` are the SMART moving-tape map of
`three-v-contains-aperiodic-rationals` and its root towers. See
`some-brin-thompson-element-factors-onto-an-odometer`, Attempts.
