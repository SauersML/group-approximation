---
rg: 2
id: thompson-f-near-eigenvectors-are-log-flat-near-the-pointer
kind: claim
title: A unit nonnegative vector on one-sided pointed forests of Thompson's F with Rayleigh value 4 - delta has E|ln(|T_(i+j)| ^ T) - ln(|T_(i+j+1)| ^ T)| <= (6+4j) sqrt(delta) ln T for every truncation T, so every log-scale ansatz whose neighbour trees are not tied at leading order is capped below 1, and Moore's two-slot tower spreads to every tree within distance about eta^(-1/4) of the pointer
distinct_from:
  thompson-f-near-eigenvectors-need-log-scale-pointer-spread: that bounds the mass crossing one dyadic scale, P(s <= t < s+r) <= 2 sqrt(delta), and sums over the scales below 2^J, so it caps only vectors with bounded pointer trees and records that it "caps neither" the log-scale continuum nor the Markov families; this integrates the same one-scale bounds against dt/t up to an arbitrary truncation T and moves them to every offset j, which caps every family whose normalized neighbour log-gap stays positive, including both classes that node leaves uncapped.
  thompson-f-near-eigenvectors-carry-a-root-local-moore-tower: that puts a tower 2 exp_(n+4)(0) at one of two slots (T_i or T_(i+15)) and says "Nothing is claimed about the trees between them"; this proves that off mass 8W(W+2) sqrt(eta) every tree T_(i+j), j <= W, has at least the square root of that size, so the tower sits at every slot of a window, and it gives a one-slot cutoff kill.
  thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit: that is a formal scale-limit computation for Markov and hidden-state size chains, with a numerical saturation near 0.978 and "ties at leading order" left as the only uncovered case; this is a rigorous, finite-volume, amplitude-free statement that ties at leading order are necessary for every Kesten witness, with weaker constants.
  thompson-f-markov-size-chain-scale-limit-affinity-at-most-0-978: that proves B <= 0.977125 for order-1 Markov chains inside the formal (E2) limit; this proves a weaker cap 1 - gamma^2/144 but for every vector with normalized neighbour log-gap gamma, of any order and at finite size, with no limit taken.
  thompson-f-near-eigenvectors-need-doubly-exponential-tree-sizes: that proves a super-Fibonacci run of log-ratios at distance O(eta^(-1/4)); this bounds the total variation of the truncated log-size profile over a window, which is consistent with that run and limits how fast it can start near the pointer.
  thompson-f-near-eigenvectors-have-fibonacci-tree-profiles: that is the level-0 profile with explicit merge tests at bounded distance; this is a scale-free integrated statement at every truncation.
  thompson-f-is-amenable: that is the open root; this is a necessary condition on its Kesten witnesses and decides nothing.
artifacts:
  - experiments/thompson-f-log-flat-window-2026-09-17/log_flat_check.py
  - experiments/thompson-f-log-flat-window-2026-09-17/log_flat_check_n9.out
---

**ESTABLISHED** (lane proof, not reviewed) by `thompson-f-near-eigenvectors-log-flat-proof`. The
imports are three ESTABLISHED nodes, quoted there. The new steps are Fubini, an elementary inequality
between logarithms, and Markov's inequality.

**Setting.** This uses the notation of `thompson-f-near-eigenvectors-need-log-scale-pointer-spread`:
- `R` is the set of one-sided pointed forests `x = (T_0, T_1, ...; i)`;
- `K = s_0 + s_0^{-1} + s_1 + s_1^{-1}`;
- `f ∈ l^2(F)` has `f ≥ 0`, `||f|| = 1` and `supp f ⊆ R`, with `μ = f^2`;
- `δ = 4 − <f, K f>` and `η = δ/4 = 1 − <f, K f>/4`.

For `j ≥ 0` put `s_j(x) = |T_{i+j}|`, the number of leaves of the tree `j` places to the right of the
pointer (`1` if it is a leaf). So `s_0 = s` and `s_1 = r` in the spread node. For a truncation
`T ≥ 1` put `L_j = ln min(s_j, T)`, which lies in `[0, ln T]`.

**Theorem 1 (log-flatness at every offset).** For every such `f`, every real `T > 1` and every `j ≥ 0`:
1. **(One scale, offset `j`.)** For every real `t`,
   - `μ(s_j ≤ t < s_j + s_{j+1}) ≤ (2 + 2j)√δ`;
   - `μ(s_{j+1} ≤ t < s_j + s_{j+1}) ≤ (4 + 2j)√δ`.
2. **(Integrated.)** `E_μ |L_j − L_{j+1}| ≤ (6 + 4j)√δ · ln T`. For `j = 0` this reads
   `E_μ |ln(s ∧ T) − ln(r ∧ T)| ≤ 6√δ ln T`.
3. **(Window.)** For every `W ≥ 1`, `E_μ Σ_{j<W} |L_{j+1} − L_j| ≤ 2W(W + 2)√δ · ln T`.

Item 1 at `j = 0` is items 1–2 of the spread node. Everything else is new.

**Corollary 2 (class kill by the neighbour log-gap).** For `T > 1` put
`γ_T(f) = E_μ |L_0 − L_1| / ln T ∈ [0, 1]` and `γ*(f) = sup_{T>1} γ_T(f)`. Then
- `δ ≥ (γ*(f)/6)^2`, that is `<f, K f>/4 ≤ 1 − γ*(f)^2/144`;
- for a signed `f` with `|f|` as above the same bound holds, since `μ = f^2` is unchanged and
  `<|f|, K|f|> ≥ <f, K f>`.

*Scale-limit form.* Let `f_k` be such vectors, `λ_k > 0`, and suppose
`(ln s/λ_k, ln r/λ_k)` under `μ_k` converges in law on `[0, ∞]^2` to `(Y, Y')`. Then

`liminf_k δ(f_k) ≥ sup_{C>0} ( E|Y ∧ C − Y' ∧ C| / (6C) )^2`,

which is positive iff `P(Y ≠ Y') > 0`. The same holds for `(ln s_j/λ_k, ln s_{j+1}/λ_k)` with `6`
replaced by `6 + 4j`.

- *Class killed:* every family of vectors on `R`, with any amplitudes and at finite size, whose
  pointer and neighbour log-sizes are not tied at leading order at some normalization `λ_k`. This
  includes:
  - product (i.i.d. size law) vectors with a non-degenerate log-scale law, such as those of
    `thompson-f-norm-bound-from-log-scale-forest-limit`. For log-uniform laws
    (`Y, Y'` i.i.d. uniform on `[0, 1]`, `C = 1`), `γ = 1/3` and the cap is `1 − 1/1296`;
  - Markov size chains of any order, multitype and hidden-state chains, and hierarchical laws, whenever
    the limiting one-step law of the log-size is not the identity.
- *Invariant:* the normalized neighbour log-gap `γ*(f)`.
- *Dying step:* the merge edge `s_1` and the pointer-right edge `s_0`. Each allows only `O(√δ)` mass to
  cross each scale `t`, and integrating over `dt/t` up to `T` turns this into a bound on the
  truncated log-gap.
- *Survivors:* only vectors with `γ*(f_k) → 0`, and by item 2 then all offsets are tied:
  `Y_0 = Y_1 = ... = Y_W` almost surely in every joint log-scale limit. So every Kesten witness is,
  at every leading log-scale, flat on every bounded window to the right of the pointer.
- This is the case "ties at leading order" that
  `thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit` leaves uncovered. It is now
  proved to be the only case left, rigorously and for every amplitude. The earlier statement was a
  formal-limit remark.

**Corollary 3 (the Moore tower fills a window).** Let `K_0` be the constant of
`thompson-f-near-eigenvectors-carry-a-root-local-moore-tower`. Let `n ≥ 0` satisfy
`12 K_0^{n+1} √η ≤ 1`, and let `W ≥ 15`. Then

`μ( ∃ j ∈ {0, ..., W} : |T_{i+j}| < exp_{n+3}(0) ) ≤ (24 K_0^{n+2} + 8W(W + 2)) √η`.

- In fact the threshold is `(2 exp_{n+4}(0))^{1/2}`, which is at least `exp_{n+3}(0)`.
- *Numbers.* Take `n = ⌊log_{K_0}(1/(96√η))⌋ − 2 ≥ 0` and `15 ≤ W ≤ η^{-1/4}/8 − 1`. Then at least
  `5/8` of the mass sits on forests where **every** tree `T_i, T_{i+1}, ..., T_{i+W}` has at least
  `exp_{n+3}(0)` leaves, with `n = log(1/η)/(2 log K_0) − O(1)`.
- Corollary B of the tower node gives this for one of the two slots `i`, `i + 15` only. Here it holds
  at all `W + 1 ≈ η^{-1/4}/8` slots at once, at the price of one level of the tower (a square root).

**Corollary 4 (one-slot cutoff kill).** Fix `j_0 ≥ 0` and put `W = max(15, j_0)`. If `μ`-almost every
`x` has `|T_{i+j_0}| < N`, then

`η ≥ (24 + 8W(W + 2))^{-2} · K_0^{−2 log* N − 4}`,

where `log* N` is the least `m` with `exp_m(0) ≥ N`. For `j_0 ≤ 15` the constant is `1/2064^2`.
- Corollary C of the tower node needs both `T_i` and `T_{i+15}` capped. Here one tree suffices,
  at any fixed offset, with the same `K_0^{−2 log* N}` shape.
- So any ansatz that caps one fixed slot (the pointer tree, say) at size `N` stays at
  `<f, K f>/4 ≤ 1 − c K_0^{−2 log* N}`, whatever the amplitudes and the other trees.

**What changes.**
- The spread node's scope line "this caps neither" the log-scale continuum nor the Markov families is
  superseded. Both are capped by Corollary 2 whenever their leading-order neighbour law is
  non-degenerate. The constants are weaker than the product cap `71/72` and the order-1 ceiling
  `0.977125`, but the class has no structural restriction at all.
- The search for Kesten witnesses is reduced to vectors whose log-size profile is flat at leading
  order on every window of width `o(δ^{-1/4})` to the right of the pointer, at every truncation.
  In such vectors, all the variation of the log-sizes near the pointer is `o(ln T)` at every scale
  `T`. This is how the tower of height `log(1/η)` must spread along the forest.
- *Consistency.* A Fibonacci run changes `ln s_j` by `O(1)` per step, and the super-Fibonacci run of
  `thompson-f-near-eigenvectors-need-doubly-exponential-tree-sizes` sits at distance
  `O(η^{-1/4})`. Item 3 allows total truncated log-variation `O(W^2 √δ ln T)`, which is `O(ln T)`
  exactly at `W ≍ δ^{-1/4}`. So the two results agree: the same window width `η^{-1/4}` appears in
  both, from different arguments.

**Scope.**
- Necessary conditions only. Nothing is proved about `||P||`, and `thompson-f-is-amenable` stays open.
- Offsets are to the right of the pointer only, since pointer-left is not total on `R`.
- The constants are not optimized. `K_0` is effective but not computed, as in the tower node.

**Computation.** `experiments/thompson-f-log-flat-window-2026-09-17/log_flat_check.py`, with output in
`log_flat_check_n9.out`. It runs on the Perron vector and a random vector of the move graph on `S_n`
windows, for `n = 2..9` (up to 11934 states). It checks, in floating point:
- item 1 at offsets `j ≤ 3`, with the sharper constants `c_M + j c_R` and `c_M + (j+1) c_R`, where
  `c_R, c_M ≤ 2√δ` are the Cauchy–Schwarz products of Step 2 of the spread route;
- the Fubini identity used in the proof, to `1e-9`;
- item 2 for `j ≤ 3` and item 3 for `W = 4`, for every integer `T ≤ n + 2`.

All pass (`ALL OK`). At these `n` the value `δ ≥ 0.88` is large, so the bounds are far from tight. The
script illustrates the chain of inequalities and certifies nothing.

Proof route: `thompson-f-near-eigenvectors-log-flat-proof`.
