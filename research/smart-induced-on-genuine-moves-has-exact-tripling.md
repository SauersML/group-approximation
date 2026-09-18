---
rg: 2
id: smart-induced-on-genuine-moves-has-exact-tripling
kind: claim
title: SMART induced on its level-zero moves is an element of 2V whose level-k sweeps take exactly 3^k steps
distinct_from:
  brin-thompson-first-return-maps-lie-in-kv: that is the general inducing tool; this names the clopen set for SMART, checks the bounded return, and proves the exact count 3^k.
  some-brin-thompson-element-factors-onto-an-odometer: that asks for an element of some kV with an odometer factor; this gives the exactly tripled candidate, and does not prove an odometer factor.
  renormalizable-thompson-elements-are-odometer-codes: that characterizes height-m renormalizations; this supplies the candidate, whose height-3 renormalization is `smart-induced-map-has-brick-local-height-3-renormalization`.
  smart-level-zero-return-map-factors-onto-3-adic-odometer: that is lane gq-nv-obstruct's independent version, which induces on all level-0 configurations (2·3^k steps per move) and proves the Z/2 x Z_3 factor (ESTABLISHED, referees a and b PASS); this induces on phase-2 leaves only (3^k steps) and adds the explicit return bound and two renormalization checkpoints.
  three-v-contains-aperiodic-rationals: that uses SMART's moving-tape map only for its lack of periodic points; this induces it on a clopen set to remove the per-level overhead.
---

**ESTABLISHED** through `smart-induced-on-genuine-moves-has-exact-tripling-proof`. Lane proof,
not independently reviewed. It rests on Callard–Salo's Proposition 3.2 and the 8-state SMART
table (arXiv:2208.00685v3, `distortion-1-smart.tex`, read from the e-print source; transcription
checked reversible in `experiments/nv-measured-walls-2026-09-17/smart_belt_periods.py`).

**Setting.** `F` is the moving-tape map of SMART on `X = {0,1,2}^Z × Q`, with
`Q = {▶_i, ◀_i, ⊳_i, ⊲_i : i = 1, 2}`. Phase-2 states move; phase-1 states read and write. The
moves `M_q(k)` of Callard–Salo's Proposition 3.2 cross a block `0^k` in `f(k) = 3^{k+1} - 2`
steps, and `f(k+1) = 3 f(k) + 4`.

**The clopen set.** Let `Y ⊆ X` consist of the phase-2 configurations that are **genuine
level-0 moves**:
- `▶_2` or `◀_2` on a nonzero cell;
- `⊳_2` whose right neighbour is nonzero;
- `⊲_2` whose left neighbour is nonzero.

**Statement.**
1. **Bounded return.** Every configuration enters `Y` within 5 steps, and the return time `r_Y`
   is at most 6. So the first-return map `S := F_Y` is conjugate by a brick-local map to an element of `2V`
   (`brin-thompson-first-return-maps-lie-in-kv`; `F ∈ 2V` by the prefix-code conjugacy of
   `three-v-contains-aperiodic-rationals-proof`, item 1, with an 8-word code on `Q`).
2. **Exact tripling.** For every `q` and `k`, and every configuration where `M_q(k)` applies,
   exactly `3^k` of the `f(k)` steps of `M_q(k)` start in `Y`. In `S`-time the level-`k` moves
   therefore take `e(k) = 3^k` steps: `e(k+1) = 3 e(k)`, with no additive defect.
3. **First renormalization check.** Let `y_{k+1}` be `▶_2` on `s_+` followed by `0^{k+1} s_*`,
   and `y_k` the same with `0^k`, for `k >= 1`.
   - `y_{k+1}` is `y_k` with one `0` inserted immediately right of the head.
   - `S^3(y_{k+1})` is `◀_2` on the pattern `s_+ 0 1 0^{k-1} s_*`, with the head on the `1`.
   - `S(y_k)` is `◀_2` on the pattern `s_+ 1 0^{k-1} s_*`, with the head on the `1`.

   So `S^3(y_{k+1})` is `S(y_k)` with one `0` inserted immediately left of the head. This is
   consistent with a height-3 renormalization whose coarsening deletes a zero next to the
   head. At the next checkpoint the correspondence is a bounded local change, but not a pure
   zero deletion.
   - `S^6(y_{k+1})` is `▶_2` on cell 1 of `s_+ 2 1 0^{k-1} s_*`.
   - `S^2(y_k)` is `⊳_2` on `s_+` in `s_+ 1 0^{k-1} s_*`.

   So the fine configuration is the coarse one with a `2` inserted right of `s_+`, the head
   moved one cell onto it, and the state changed from `⊳` to `▶`. Along the fine run the states
   at the `Y`-visits are `▶◀⊳ ◀▶⊲ ▶…`. These are the images `σ(▶) σ(◀) σ(⊳)…` of the coarse
   sequence `▶◀⊳…` under the substitution of `smart-level-zero-return-map-factors-onto-3-adic-odometer`
   (`▶ ↦ ▶◀⊳`, `◀ ↦ ◀▶⊲`, `⊳ ↦ ▶⊲⊳`, `⊲ ↦ ◀⊳⊲`). The first letters `▶, ◀, ▶` are the states at
   `S^0, S^3, S^6`.

**Renormalization, now established.** A clopen `A` and a brick-local `φ` with `S^3 = φ^{-1} S φ`
on `A` and `X_Y = A ⊔ SA ⊔ S^2 A` are given by `smart-induced-map-has-brick-local-height-3-renormalization`,
for this induced element (called `U` there). That node is ESTABLISHED and refereed PASS by gq-referee-a
(12b5beb4a), gq-referee-b (b6d33ae8e) and gq-referee-c
(`gq-referee-c-smart-induced-map-has-brick-local-height-3-renormalization.md`). Item 2 and the two
checkpoints in item 3 were the first evidence for it. Lane gq-nv-obstruct's substitution route, for the map
induced on all level-0 configurations, is `smart-level-zero-return-map-factors-onto-3-adic-odometer`
(ESTABLISHED).
