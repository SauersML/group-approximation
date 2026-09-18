---
rg: 2
id: smart-induced-on-genuine-moves-has-exact-tripling
kind: claim
title: SMART induced on its level-zero moves is an element of 2V whose level-k sweeps take exactly 3^k steps
distinct_from:
  brin-thompson-first-return-maps-lie-in-kv: that is the general inducing tool; this names the clopen set for SMART, checks the bounded return, and proves the exact count 3^k.
  some-brin-thompson-element-factors-onto-an-odometer: that asks for an element of some kV with an odometer factor; this gives the exactly tripled candidate, and does not prove an odometer factor.
  renormalizable-thompson-elements-are-odometer-codes: that characterizes height-m renormalizations; this supplies the candidate whose renormalization identity is still to be checked.
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
   head. At the next checkpoint the correspondence is no longer a pure zero deletion.
   `S^6(y_{k+1})` is `⊲_2` on the second cell of `s_+ 1 1 0^{k-1} s_*`, while `S^2(y_k)` is
   `⊳_2` on `s_+` in `s_+ 1 0^{k-1} s_*`. A coarsening there must also change the state and move
   the head two cells.

**Not established.** A clopen `A` and a brick-local `φ` with `S^3 = φ^{-1} S φ` on `A` and
`X_Y = A ⊔ SA ⊔ S^2 A`. The same goes for any continuous eigenvalue `e^{2πi/3}` of `S`. The
evidence is only item 2 together with the two checkpoints in item 3. The substitution route
of lane gq-nv-obstruct (`some-brin-thompson-element-factors-onto-an-odometer`, Attempts) decides
the eigenvalue question independently.
