---
rg: 2
id: brick-groupoid-has-zn-cocycle-with-af-kernel
kind: claim
title: "The brick groupoid G_2^n carries a continuous Z^n-valued cocycle whose kernel is an AF groupoid, so nV is the full group of an AF-by-Z^n groupoid"
distinct_from:
  brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination: that is a group-level splitting of the Haagerup property of nV along the exponent cocycle and its locally finite kernel; this is the groupoid-level fact that the kernel subgroupoid is AF, which is what a hypothesis list can quantify over.
  matui-sft-groupoid-homology-is-k-theory: that computes the homology of a one-sided SFT groupoid; this records the AF kernel of the canonical cocycle and its product form.
artifacts: []
---

**Status: OPEN** (demoted 2026-09-18 at landing, procedurally). The claim was posted in
a batch with `nv-brick-groupoid-and-kazhdan-host-are-both-o2` and two of three referees
voted refuted — **but no refutation touched this claim**; all three lenses checked this
route and found every step correct, and lens 2 recorded it as "clean and import-free".
Its route therefore requires only the procedural gap
`brick-af-cocycle-referee-confirmation`, a per-claim referee pass. See `## Attempts`.

## Statement

Let `C = {0,1}^N` and let

`G_2 = {(x, k - l, y) ∈ C × Z × C : σ^k(x) = σ^l(y)}`

be Matui's groupoid of the one-sided full 2-shift, with `c(x, m, y) = m`. For `n ≥ 1` put

`c^{(n)} : G_2^n → Z^n`, `c^{(n)}(g_1, …, g_n) = (c(g_1), …, c(g_n))`.

Then:

1. `c^{(n)}` is a continuous groupoid cocycle (`c^{(n)}(gh) = c^{(n)}(g) + c^{(n)}(h)`);
2. `ker c^{(n)} = R_2^n`, where `R_2 = {(x, 0, y) : ∃k, σ^k x = σ^k y}` is the tail
   equivalence relation of `C`;
3. `R_2^n` is an AF groupoid: it is the increasing union of the elementary (compact open,
   principal, finite-orbit) subgroupoids `R_k^n` with
   `R_k = {(x,0,y) : x_i = y_i for all i ≥ k}`;
4. hence `G_2^n` is an ample, Hausdorff, second countable, minimal, effective, purely
   infinite groupoid carrying a continuous `Z^n`-cocycle with AF kernel, and
   `nV ≤ [[G_2^n]]`.

## Why it is recorded

This is the "surviving lever" named in the Attempts of
`brin-thompson-groups-nv-are-a-t-menable` ("`G_2^n` carries a continuous `Z^n`-cocycle
with AF kernel"), written out as a node so that a hypothesis list can quantify over it.
It is the hypothesis of `af-by-zk-full-groups-have-finite-kazhdan-subgroups`, the one
groupoid-level property of `G_2^n` that the recorded Kazhdan hosts are not known to
share; see that node for the state of the separation.

## Attempts

- **2026-09-18 (e2-w2-nv-separate): direct route `brick-groupoid-zn-cocycle-af-kernel-proof`,
  checked by three referee lenses, no defect found, demoted only because the batch vote
  went against a different claim.** What each lens verified:
  - `c(x,m,y) = 0` forces `m = 0`, hence `k = l`, so `ker c` is exactly equal-level tail
    equivalence — the step is not merely "some `k, l`" but the genuine equal-level
    relation (lenses 1, 2, 3).
  - `R_k = ⋃_{|μ|=|ν|=k} U_{μ,ν}` is compact open, principal, with orbits of constant
    size `2^k`, hence elementary, and `R_k^n` increases to `R_2^n` (lenses 1, 2).
  - Products of AF groupoids are AF, and the C*-side cross-check — the UHF core
    `M_{2^∞}^{⊗n}` realized as the `T^n`-gauge fixed-point algebra — is consistent
    (lens 1).
  - **Where it stops:** nothing mathematical. The votes were cast on the batch, which was
    refuted at Step 5 of the `O_2` computation (lens 2) and at the gate wording of
    `brin-thompson-groups-nv-are-a-t-menable` (lens 3). A per-claim vote has not been
    recorded, and that is the whole content of
    `brick-af-cocycle-referee-confirmation`.
