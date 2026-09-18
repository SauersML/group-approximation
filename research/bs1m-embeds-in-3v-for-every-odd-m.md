---
rg: 2
id: bs1m-embeds-in-3v-for-every-odd-m
kind: claim
title: For every odd m >= 3 the Baumslag-Solitar group BS(1,m) embeds in the Brin-Thompson group 3V
distinct_from:
  bs13-embeds-in-brin-thompson-3v: that is the case m = 3, established through SMART; this is every odd m, through the machines M_m.
  bs12-embeds-in-brin-thompson-2v: that asks for m = 2; even m stays blocked for all-crossing hierarchies by crossing-move-hierarchies-have-odd-branching, so this claim does not reach it.
  smart-type-machines-branch-by-every-odd-number: that supplies the machines M_m and their timing; this is the group-theoretic target.
  bs-1-m-embeds-in-brin-thompson-3v-for-odd-m: that is the same statement, proved by lane bh-free-18 through its family SMART_m; this node is a pointer to it, recording an independent family and numerical evidence.
artifacts:
  - research/artifacts/gq-affq-odd-branching-machines.md
---

**ESTABLISHED** through `bs1m-embeds-in-3v-for-every-odd-m-via-smart-m`: this is the statement of
`bs-1-m-embeds-in-brin-thompson-3v-for-odd-m`, proved by lane bh-free-18 (cbf8ec85c) with the machines
`SMART_m`. This node is kept as a **pointer**. The route and evidence below are an independent second family
`M_m` with the same timing but a different table (see `smart-type-machines-branch-by-every-odd-number`), plus
whole-tape numerical checks. The checks are independent evidence for the pipeline, not a proof for `M_m`.

The statement: for every odd `m ≥ 3` there are `s, u ∈ 3V` with `s` of infinite order and `u s u^{-1} = s^m`. Hence
`BS(1,m) ≤ 3V`.

**Alternative route through `M_m` (the SMART pipeline, run with m in place of 3; not proved for `M_m`).**
1. The machine `M_m` of `smart-type-machines-branch-by-every-odd-number`: two shapes, `m` symbols, reversible,
   with exact `m`-fold crossing timing. Its moving-tape map lies in `2V` by the prefix-code conjugacy.
2. Induce on SMART's genuine level-0 moves `Y` (bounded return), which gives `U ∈ 2V`
   (`brin-thompson-first-return-maps-lie-in-kv`). Each level-`L` crossing then takes exactly `m^L` steps of `U`.
3. A brick-local height-`m` renormalization `φ` of `U`.
4. `renormalizable-thompson-elements-give-baumslag-solitar`.

**Evidence for m = 5** (artifact §4–§5; MSI; calibrated on SMART, where the proved `m = 3` rule is recovered).
- Step 1: timing verified for `L ≤ 7`.
- Step 2: `N_Y(L) = 5^L` exactly.
- The induced map has locally readable eigenvalues `−1`, `e^{2πi/5}` and `e^{2πi/25}` at radii 0, 1 and 2.
- Step 3: in every class of the Z/5 phase, a one-cell-deletion rule on radius-2 windows passes all of about
  11,000 exact whole-tape validations of `φ S^5 = S φ`, with no failures.

**Gaps.**
- The move lemma for `M_m` (timing for all `L`).
- An explicit rule for `φ`, with its bijectivity.
- A proof of `φ U^m = U φ` on all configurations, as gq-nv-obstruct gave for SMART (induction over the move
  hierarchy, plus density for the limiting configurations).
- For `m ≥ 7`, the pipeline has not been run.

If the claim holds, `3V` contains `BS(1,m)` for infinitely many `m`. It does not reach `BS(1,2)`.
