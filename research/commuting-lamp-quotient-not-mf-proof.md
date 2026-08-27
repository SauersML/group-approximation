---
rg: 2
id: commuting-lamp-quotient-not-mf-proof
kind: route
title: The tau-moved root lamp is an involutive compression witness
target: commuting-lamp-quotient-not-mf
requires: [commuting-lamp-quotient-structure, compression-torsion-collapse]
artifacts:
  - GroupApproximation/Sofic/InvolutionCollapseEndpoint.lean
---

## Why sufficient

By `commuting-lamp-quotient-structure`,
`W/<zeta> = F_2[X] semidirect V` with site set `X = V/Gbar`, root `o`,
shift `tau`, and all lamps commuting.  Apply the involutive collapse — the
formalized endpoint
`InvolutionCollapseEndpoint.actualCoronaMFInvisible_of_involutiveWitness`
behind `compression-torsion-collapse` — with ambient `H = W/<zeta>`,
Kazhdan subgroup `L` the image of `Gbar` (property (T) passes to images),
compressor `s = tau` (`tau Gbar tau^{-1} <= Gbar` is the defining
stable-letter relation), and witness `k = c_{tau o}`, the lamp at the
shifted root:

- (W1) `k^2 = 1`: lamps are involutions in `W/<zeta>`.
- (W2) `[s L s^{-1}, k] = 1`: the stabilizer of the site `tau o` in `V` is
  exactly `tau Gbar tau^{-1}`.
- (W3) the `L`-conjugates of `k` are lamps, and ALL lamps of `W/<zeta>`
  commute.

The collapse theorem places `[gamma, k]` in `Rad_MF(W/<zeta>)` for every
`gamma in L`.  Take `gamma = v_1`: the sites `v_1 tau o` and `tau o` are
distinct — this is the formalized two-site separation of the linear model
(`D^{-1} v_1 D` has the entry `1/2`) — so

```text
[v_1, c_{tau o}] = c_{v_1 tau o} c_{tau o} != 1
```

in the elementary abelian lamp kernel.  A nontrivial element of the
radical makes every corona representation non-injective.

**Consistency checks.**  The defect is a level-one two-lamp configuration,
hence lies in the level-even subgroup `L_0`, consistent with
`corona-hs-radical-is-finite-residual` (the radical is a `V`-submodule of
`L_0`).  No conflict with `marked-quotients-not-lef`: nothing here
produces finite models.
