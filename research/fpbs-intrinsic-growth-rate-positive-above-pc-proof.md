---
rg: 2
id: fpbs-intrinsic-growth-rate-positive-above-pc-proof
kind: route
title: Anchored expansion makes every intrinsic ball of a large enough radius grow by a fixed factor per step, and Fatou turns this into a positive expected rate
target: fpbs-intrinsic-growth-rate-positive-above-pc
requires:
  - fpbs-hermon-hutchcroft-anchored-expansion
  - fpbs-intrinsic-l2-rate-closed-zero-set
  - fpbs-intrinsic-rates-log-lipschitz-in-parameter
---

Complete written proof. No computation is used. Notation as in the claim.

**What is used.**

- From `fpbs-intrinsic-l2-rate-closed-zero-set`, item 1 only (BK
  submultiplicativity in `R`), which gives that `lambda_1(t)` exists as a limit
  and equals `inf_R R^(-1) log E_t|B^int_R(o)|`. Item 1's proof does not use
  the step corrected in `fpbs-intrinsic-rates-log-lipschitz-in-parameter`.
- From `fpbs-intrinsic-rates-log-lipschitz-in-parameter`, item 3:
  `lambda_1 = 0` on `[0,p_c]`, continuity, and `lambda_1(t) <= log(t/p_c)`.
- From `fpbs-hermon-hutchcroft-anchored-expansion`: for `p_c < t <= 1`,
  almost surely every infinite cluster `K` has `Phi*_E(K) > 0`. A Cayley graph
  is connected, locally finite and transitive, and it is nonamenable as a graph
  because `Gamma` is nonamenable.

**Step 1 (a deterministic growth lemma).** Let `K` be an infinite, connected
graph with maximal degree at most `D`, let `o in V(K)`, and suppose there are
`phi > 0` and `N_0` such that every connected `S ⊆ V(K)` with `o in S` and
`N_0 <= |S| < infinity` satisfies `|d_E S| >= phi |S|`. Write `B_R` for the
ball of radius `R` about `o` in the graph metric of `K`. Then
`|B_R| >= (1 + phi/D)^(R - N_0)` for every `R >= N_0`.

*Proof.*

- `B_R` is finite (local finiteness), contains `o`, and is connected, because
  it is a union of geodesics from `o`.
- `B_(R+1)` strictly contains `B_R`. Otherwise no edge leaves `B_R`, so
  `B_R` is a connected component of `K`; it is finite while `K` is infinite and
  connected, which is impossible. Hence `|B_R| >= R + 1`, and `|B_R| >= N_0`
  when `R >= N_0`.
- Let `e = {u,w}` be an edge of `d_E B_R` with `u in B_R` and `w` not in
  `B_R`. Then `R < d(o,w) <= d(o,u) + 1 <= R + 1`, so `w in B_(R+1) \ B_R`.
  Each such `w` is an endpoint of at most `D` edges. Hence
  `|B_(R+1) \ B_R| >= |d_E B_R| / D`.
- For `R >= N_0` this gives `|B_(R+1)| >= |B_R| + (phi/D)|B_R|`. Induction
  from `|B_(N_0)| >= 1` gives the bound.

**Step 2 (the anchored hypothesis holds on a set of positive probability).**
Fix `t in (p_c,1]`. Then `theta(t) = P_t(|K_o| = infinity) > 0`, by the
definition of `p_c` and monotonicity. By the imported corollary,
`Phi*_E(K_o) > 0` almost surely on `{|K_o| = infinity}`. So by continuity of
measure there is `phi > 0` with
`P_t(E_phi) > 0`, where `E_phi = {|K_o| = infinity, Phi*_E(K_o) > 2 phi}`.

On `E_phi`, the infimum in the definition of `Phi*_E(K_o)` is nondecreasing in
`n` and its limit exceeds `2 phi`. So there is a finite random
`N_0(omega)` such that every connected `S` of `K_o` with `o in S` and
`N_0 <= |S| < infinity` satisfies `|d_E S| >= phi sum_(u in S) deg_K(u)`.
Every vertex of the infinite connected cluster has `deg_K(u) >= 1`, and
`deg_K(u) <= D`. So the hypothesis of Step 1 holds for `K = K_o` with this
`phi` and `N_0(omega)`. The intrinsic ball `B^int_R(o)` is the ball `B_R` of
Step 1 for `K = K_o`.

**Step 3 (from almost-sure growth to the expected rate).** Fix `epsilon in
(0,1)`. On `E_phi ∩ {N_0 <= epsilon R}` Step 1 gives
`|B^int_R(o)| >= (1 + phi/D)^((1-epsilon) R)`. Hence

```text
E_t |B^int_R(o)| >= (1 + phi/D)^((1-epsilon) R) P_t(E_phi ∩ {N_0 <= epsilon R}).
```

Since `N_0 < infinity` on `E_phi`, the probability tends to
`P_t(E_phi) > 0` as `R -> infinity`. Taking `R^(-1) log` and letting
`R -> infinity` gives `lambda_1(t) >= (1-epsilon) log(1 + phi/D)`. Letting
`epsilon -> 0` gives item 1:
`lambda_1(t) >= log(1 + phi/D) > 0`. Because
`lambda_1(t) = inf_R R^(-1) log E_t|B^int_R(o)|`, this also gives
`E_t|B^int_R(o)| >= e^(lambda_1(t) R)` for every `R >= 1`.

**Step 4 (item 2).** Item 1 gives `lambda_1 > 0` on `(p_c,1]`, so
`p_lambda1 <= p_c`. The imported item 3 of
`fpbs-intrinsic-rates-log-lipschitz-in-parameter` gives `lambda_1 = 0` on
`[0,p_c]`, continuity and the upper bound. So `p_lambda1 = p_c`. QED.

**Check on `T_d`.** The recorded value `lambda_1(t) = max(0, log(t(d-1)))`
vanishes exactly on `[0, 1/(d-1)] = [0,p_c]`, as item 2 requires. No step uses
it.
