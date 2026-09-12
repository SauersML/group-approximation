---
rg: 2
id: periodic-approximable-subshifts-host-no-fp-simple-group-proof
kind: route
title: Periodic points of the SFT neighbourhood give finite quotients
target: periodic-approximable-subshifts-host-no-fp-simple-group
requires:
  - fp-subshift-full-group-subgroups-extend-to-sft
artifacts:
  - research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md
---

## Why sufficient

1. **Finite orbits in the neighbourhood.** Let `Gamma` be a finitely generated,
   finitely presented, infinite simple subgroup of `[[Lambda ~ X]]`. The
   prerequisite gives an SFT `Y ⊇ X`, cut out by allowed patterns on a finite
   shape `K`. Every `K`-pattern of `X` is allowed, and the extended generators
   fix every finite orbit of `Y` pointwise.
2. **A moved finite orbit.** Some generator `g_i` moves some `x` with cocycle
   `n = c_i(x|_D) != e`. Apply (PA) with `W ⊇ D`, `K`, and `B = {n}`. The
   resulting `y` lies in `Y`, has a finite orbit, and
   `hat g_i(y) = n . y != y`. This contradicts step 1.
3. **Minimal Z-subshifts have (PA).**
   - An infinite minimal subshift contains no periodic point, so its action is
     free.
   - Choose `N` with `W ⊆ [-N, N]` such that `x|_{[-N,N]}` is not `d`-periodic
     for `d <= max |B|`. This is possible because `x` is not periodic.
   - Uniform recurrence places `v = x|_{[-N, N+2M]}` again at some shift
     `q > 2N+2M+1`.
   - The `q`-periodic `y` with `y|_{[-N, -N+q)} = x|_{[-N, -N+q)}` equals `x` on
     `[-N, N+2M+q]`. So its windows of length `2M+1` occur in `x`, and its least
     period exceeds `max |B|`.
