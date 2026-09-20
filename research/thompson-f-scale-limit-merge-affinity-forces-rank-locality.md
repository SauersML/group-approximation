---
rg: 2
id: thompson-f-scale-limit-merge-affinity-forces-rank-locality
kind: claim
title: In the log-scale limit every stationary pointed-forest law (any memory, hidden types or hierarchy) has merge affinity B at most 1 - 0.257 delta^2, where delta is the mean rank step between neighbouring trees, by the exact identity U + D = 1 - c' with c the level-crossing rate; so B -> 1 forces rank-local laws, and for size-only split laws B is bounded by a three-point functional that is exact on Markov chains
distinct_from:
  thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit: that gives (E2), the numerics near 0.955 and the necessary condition U + D -> 1 in L^1; this proves U + D is pinned to the level-crossing rate for every stationary process, which turns that condition into rank-locality with an explicit rate, and adds a three-point bound valid for every memory depth.
  thompson-f-markov-size-chain-scale-limit-affinity-at-most-0-978: that caps order-1 Markov chains by a CDF identity that uses the Markov property (p_{++} = E[U(1-D)]); this identity uses stationarity only, so it covers all memory, but it gives a ceiling only away from the rank-local regime.
  thompson-f-iid-forest-test-vectors-are-bounded-below-one: that is product laws on finite windows; this is arbitrary stationary laws in the formal scale limit.
  thompson-f-is-amenable: the root is untouched; this narrows the size-only test-vector programme to rank-local laws.
artifacts:
  - experiments/thompson-f-three-point-scale-2026-09-17/three_point_bound.py
  - experiments/thompson-f-three-point-scale-2026-09-17/four_point_bound.py
  - experiments/thompson-f-three-point-scale-2026-09-17/rank_locality_check.py
  - experiments/thompson-f-three-point-scale-2026-09-17/local_problem.py
  - experiments/thompson-f-three-point-scale-2026-09-17/opt_small.out
  - experiments/thompson-f-three-point-scale-2026-09-17/opt_mid.out
  - experiments/thompson-f-three-point-scale-2026-09-17/opt4.out
  - experiments/thompson-f-three-point-scale-2026-09-17/opt_local.out
  - experiments/thompson-f-three-point-scale-2026-09-17/opt_localsym.out
  - experiments/thompson-f-three-point-scale-2026-09-17/three_point_check.out
  - experiments/thompson-f-three-point-scale-2026-09-17/four_point_check.out
  - experiments/thompson-f-three-point-scale-2026-09-17/local_check.out
  - experiments/thompson-f-three-point-scale-2026-09-17/rank_locality_check.out
---

**ESTABLISHED** (direct proof, unrefereed) for Theorem parts 1–4, inside the formal log-scale limit (E2).
The question in **Open** (whether `sup Φ_3 < 1`) is not settled; the numbers recorded there are evidence.

**Scope.** Everything here is about the formal functional (E2) of
`thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit`:
- sizes are rescaled log-sizes `y = log n / log M`, with `M → ∞` taken formally;
- merge acts as `max`;
- a split of level `m` has one child at level `m` and one child at level `s < m`, on the left or on the right.

Nothing here is about finite `M`, finite windows or `||P||`.

**Setting.** Take a stationary law of pointed forests with `BC_shift = 1`. Let `(X_t)` be its size
process (stationary). Assume that the marginal of `X_0` has no atoms and that `P(X_0 = X_1) = 0`.
- `π` is the marginal law; `F` is its CDF; `V_t = F(X_t)` is the *rank* of tree `t`, which is uniform on `[0,1]`.
- `U(m) = P(X_{-1} < m | X_0 = m)`, `D(m) = P(X_1 < m | X_0 = m)`, `S = U + D ∈ [0, 2]`.
- `δ = E|V_1 − V_0|` is the *mean rank step*.
- `c(e) = P(V_0 < e ≤ V_{-1})` is the rate of down-crossings of rank level `e`.
- `B` is the (E2) merge affinity, and the Rayleigh value is `R = (1 + B)/2`.

Monotone reparametrisations of `y` change none of `U, D, S, B`, so we may and do work in rank coordinates,
where `π` is Lebesgue measure on `[0,1]`.

**Theorem.**
1. **(Size projection, all laws.)** `B ≤ E_π √S`.
2. **(Crossing identity, all stationary processes.)** For a.e. rank level `v`, `S(v) = 1 − c'(v)`. Here
   `c` is Lipschitz, `c(0) = c(1) = 0`, `c ≥ 0` and `∫_0^1 c = δ/2`. Consequently:
   - `E[S] = 1`;
   - `Cov(S, V) = δ/2`;
   - `Var S = ∫_0^1 c'(v)^2 dv ≥ 3 δ^2`.
3. **(Rank-locality.)**
   `B ≤ ∫_0^1 √(1 − c'(v)) dv ≤ 1 − Var(S)/(2(1+√2)^2) ≤ 1 − 3δ^2/(2(1+√2)^2) = 1 − 0.25736 δ^2`.
   So `R ≤ 1 − 0.12868 δ^2`, and `B ≥ 1 − η` forces `δ ≤ 1.972 √η`.
4. **(Window bounds for size-only split laws.)** Suppose that, given all sizes, the top split
   `(side, s)` of `T_0` depends only on `X_0 = m`, through a law `κ(side, s | m)`. This is the (E1)
   family with an arbitrary stationary size process: order-`k` chains, hidden-state size chains, and so on.
   Write `p_k` for the density of `(X_{-1}, …, X_{k-2})`, taken with respect to any common dominating
   measure. Put:
   ```
   c3_L(s,m) = ∫ √(p3(a,s,m) p2(a,m)) da,              c3_R(s,m) = ∫ √(p3(m,s,b) p2(m,b)) db,
   c4_L(s,m) = ∫∫ √(p4(a,s,m,b) p3(a,m,b)) da db,      c4_R(s,m) = ∫∫ √(p4(a,m,s,b) p3(a,m,b)) da db,
   Φ_k = ∫ dm ( ∫_{s<m} [ ck_L(s,m)^2 + ck_R(s,m)^2 ] ds )^{1/2}.
   ```
   Then `B ≤ Φ_4 ≤ Φ_3 ≤ E_π √S`. For a stationary order-1 chain, `Φ_3` equals the (E2) value `B`
   exactly.

**What is new.** Part 2 uses stationarity only, not the Markov property.
- It explains the saturation mechanism seen in all the numerics.
- `U + D` is not a free function. It is `1` minus the derivative of the level-crossing rate.
- A law with `U + D ≡ 1` would need no crossings at all, and a stationary process cannot do that.
- The only way to make `S` nearly constant is to make every crossing rate nearly constant in the level.
  That forces `c` to be small, since it vanishes at both ends and is Lipschitz with a small derivative.
- A small `c` means a small `δ`: neighbouring trees have nearly equal *ranks*.

This turns the heuristic "ties at leading order are the only place left" (hidden-state Attempt on
`thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit`) into a theorem with a rate. It applies
to every memory depth, to hidden types and to hierarchies alike, because part 1 reads only sizes.

## Proof

*Rank coordinates.* `F` is continuous because `π` has no atoms, so `V_t = F(X_t)` is uniform. `F` is flat
only on countably many open intervals, each of `π`-mass `0`. So almost surely `X_i < X_j ⟺ V_i < V_j`
for all `i, j`. Hence `U, D, S` (read at `X_0`) and every order statistic of the process are unchanged when
`X` is replaced by `V`. The (E2) functional reads only the order of sizes, since merge acts as `max` and a
split keeps the level `m`, and it is invariant under monotone maps of `y`. From here on, `π` is Lebesgue
measure on `[0,1]` and `X = V`.

*Part 1 (data processing onto the pointer tree's top split).* `B` is the Bhattacharyya affinity between the
law `Q` of configurations and its image `x_1 Q` under the merge, computed in the limit (E2). Map every
configuration to `(side, s, m)`: the side of the small child of the pointer tree, the small child's level
and the pointer tree's level. The Bhattacharyya affinity can only grow under a measurable map.
- Under `Q`, the triple has law `κ̄(side, s | m) dm`, where `κ̄` is the split law of `T_0` given its size.
  No assumption on `κ̄` is needed.
- Under `x_1 Q`, the pointer tree is `(T_0, T_1)`, with level `max(X_0, X_1)`. Its small child is `T_0`
  (side `L`) when `X_0 < X_1`. So the triple has density `p2(s,m)` on side `L` and `p2(m,s)` on side `R`,
  for `s < m`. Here `p2` is the density of `(X_0, X_1)`, which is also the density of `(X_{-1}, X_0)`.

By Cauchy–Schwarz over `(side, s)` for each fixed `m`, using `Σ_side ∫ κ̄ ds = 1`,
```
B ≤ ∫ dm Σ_side ∫ ds √(κ̄ · p2) ≤ ∫ dm ( ∫_{s<m} [p2(s,m) + p2(m,s)] ds )^{1/2} = ∫ √(U(m) + D(m)) dm.
```
The last step uses `∫_{s<m} p2(s,m) ds = P(X_0 < m | X_1 = m) = P(X_{-1} < m | X_0 = m) = U(m)` (with
`π ≡ 1`) and, similarly, `∫_{s<m} p2(m,s) ds = D(m)`. This is (E3) of the Markov node with the Markov
hypothesis removed.

*Part 2 (crossing identity).* Fix `e ∈ [0,1]`. Then:
- `∫_0^e S(v) dv = E[S(X_0); X_0 < e] = P(X_{-1} < X_0 < e) + P(X_1 < X_0 < e)`;
- by stationarity (shift by `−1`), `P(X_1 < X_0 < e) = P(X_0 < X_{-1} < e)`;
- the sum is therefore `P(X_{-1} < e, X_0 < e)`, because ties have probability `0`;
- and `e = P(X_0 < e) = P(X_{-1} < e, X_0 < e) + P(X_0 < e ≤ X_{-1})`.

Subtracting gives `∫_0^e (1 − S) = c(e)` for every `e`.

It follows that:
- `c` is Lipschitz: `|c(e') − c(e)| ≤ P(X_0 ∈ [e,e')) + P(X_{-1} ∈ [e,e')) ≤ 2|e' − e|`;
- `c' = 1 − S` almost everywhere;
- `c(0) = 0` and `c(1) = P(X_0 < 1 ≤ X_{-1}) = 0`, which is `E S = 1`.

By Fubini, `∫_0^1 c(e) de = E[(X_{-1} − X_0)^+] = δ/2`, since `E[X_{-1} − X_0] = 0`. Integrating by
parts,
`δ/2 = ∫ c = −∫ v c'(v) dv = −∫ (v − 1/2) c'(v) dv = ∫ (v − 1/2)(S − 1) dv = Cov(S, V)`,
and `Var S = ∫ c'^2`. Cauchy–Schwarz with `Var V = 1/12` gives `(δ/2)^2 ≤ Var S / 12`.

*Part 3.* Part 1 with `S = 1 − c'` gives the first inequality. For `S ∈ [0,2]`,
```
√S − 1 − (S − 1)/2 = −(√S − 1)^2/2 = −(S − 1)^2 / (2(√S + 1)^2) ≤ −(S − 1)^2 / (2(1 + √2)^2).
```
Take expectations, use `E S = 1`, and then apply part 2.

*Part 4.* The argument is data processing onto `(side, s, m, a, b)`: the side and level of the small child,
the pointer tree's level, and the levels of its two neighbours.
- Under `Q`, `(a, m, b) = (X_{-1}, X_0, X_1)` has density `p3(a,m,b)`. By hypothesis, the split `(side, s)`
  of `T_0` is drawn from `κ(· | m)` independently of the neighbours.
- Under `x_1 Q`, the neighbours of the merged tree are `X_{-1}` and `X_2`. So the tuple has density
  `p4(a,s,m,b)` on side `L` (the unmerged window `(a, s, m, b)`, with `s < m`), and `p4(a,m,s,b)` on side
  `R`.

Hence `B ≤ ∫ dm Σ_side ∫ ds √κ(side,s|m) · c4_side(s,m)`. Cauchy–Schwarz over `(side, s)` gives `Φ_4`.

Next, Cauchy–Schwarz in the far neighbour gives `c4 ≤ c3` pointwise:
- for `c4_L`, integrate over `b`, using `∫ p4(a,s,m,b) db = p3(a,s,m)` and `∫ p3(a,m,b) db = p2(a,m)`;
- for `c4_R`, integrate over `a`, using `∫ p4(a,m,s,b) da = p3(m,s,b)` and `∫ p3(a,m,b) da = p2(m,b)`.

This gives `Φ_4 ≤ Φ_3`.

Finally, Cauchy–Schwarz in the near neighbour gives `c3_L(s,m)^2 ≤ p2(s,m) · 1` and
`c3_R(s,m)^2 ≤ p2(m,s) · 1`, so `Φ_3 ≤ ∫ √S`, as in part 1.

*Exactness on Markov chains.* In an order-1 chain, the law of `X_{-1}` given `(X_0, X_1) = (s, m)` is `r_s`.
So `c3_L(s,m) = √(p2(s,m)) BC(r_s, r_m)` and `c3_R(s,m) = √(p2(m,s)) BC(f_s, f_m)`. With `J = p2` and
`π ≡ 1`, `Φ_3` is then literally the (E2) formula of the Markov node.

## Consequences

- **Decomposition of the size-only programme.** A size-only test vector with `B → 1` in (E2) must be a
  sequence of laws with `δ → 0`. The ranks of neighbouring trees must agree to within `o(1)`, and by
  part 3 the defect is at least `0.257 δ^2`. Every law with `δ ≥ δ_0` is capped at `1 − 0.257 δ_0^2`,
  whatever its memory. What remains is one regime, and its prerequisites can fail independently:
  - **(P1)** The rank-local limit problem (below) has value `< 1`.
  - **(P2)** Localisation: as `δ → 0`, `sup Φ_3` is governed by that local problem.
  - **(P3)** For laws whose splits see hidden types or neighbours, part 4 is not available, and only
    `B ≤ E√S` is proved. Such laws need their own window bound.
- **Why Markov and the census saturate.** The order-1 Markov optimum has a large rank step, so part 3 alone
  already caps it away from `1`. Denser memory does not reduce `δ` by itself, because `S` is tied to the
  crossings of `V`, not to the kernel's order.
- **What part 2 says about ties.** In the ties regime, the drift remark of earlier waves
  (`1 − B ≳ (Eφ / ratio-range)^2` for a monotone push) becomes a special case: a push is a crossing-rate
  gradient, and the loss `∫ (c')^2` is at least its square.

## Open: the rank-local limit problem

*Local problem.* Rank-locality says that, near a rank level `m`, the process looks like a walk on the
line with stationary increments and locally flat marginal. Discretise the level into unit bins with
uniform jitter inside each bin (as in `three_point_bound.py`). Let the increments form a stationary chain
`K` on `{−L..L}` with law `g` and pair law `h = g K`. Per unit of level mass, the bin formula of part 4
becomes
```
c_L(d) = Σ_t √(h[t,d] g[t+d]),   c_R(d) = Σ_w √(h[−d,w] g[w−d]),   C(d) = c_L(d)^2 + c_R(d)^2,
Ψ = (2/(3C(0))) ((A + C(0))^{3/2} − A^{3/2}),   A = Σ_{d≥1} C(d).
```
- `Ψ ≤ 1` by Cauchy–Schwarz. Locally `S ≡ 1`, so part 3 gives nothing here, and all of the defect comes
  from the Bhattacharyya factors.
- Exact equality would need *valley-deletion invariance*: at a local minimum `s` between neighbours
  `a, m`, the density `h` must equal both `g(m−s) g(a−m)` and `g(a−s) g(m−a)`. So `g(m−s) = g(a−s)`
  whenever `a − m` is an increment, and no probability density `g` can do that.
- The question is whether multi-scale laws can make the mismatch vanish in the limit.
- `local_problem.py check` realises mirror-symmetric (drift-free) `K` by long reflected strips of the
  global problem. The strip values `0.839509, 0.836812, 0.835570` at `N = 20, 40, 80` converge to
  `Ψ = 0.834392` at rate `O(1/N)` (`local_check.out`). So symmetric local values are lower bounds for
  `sup Φ_3`.

## Numerics

All values are L-BFGS maxima over several starts, so they are lower bounds for the true suprema of each
finite family. Each family sits inside the next as `N` or `L` grows. The product value
`2√2/3 = 0.942809` is a saddle that some starts reach.

*Global three-point bound* `sup Φ_3` over order-2 bin chains on `N` bins (`opt_small.out`, `opt_mid.out`).
This bounds `B` for every size-only split law whose 3-point law is piecewise constant on `N` bins.

| N | sup Φ_3 | δ of optimiser | true order-2 B of the optimiser |
|---|---|---|---|
| 3 | 0.956728 | 0.2445 | 0.923073 |
| 4 | 0.960093 | 0.2230 | 0.913957 |
| 6 | 0.964118 | 0.1946 | 0.896470 |
| 8 | 0.966443 | 0.1758 | not computed |
| 12 | 0.969043 | not computed | not computed |

- The optimisers become rank-local: `δ` falls steadily with `N`, from `0.245` at `N = 3` to `0.176` at
  `N = 8`. This is slower than `N^{-1/2}`, since `δ√N` rises from `0.42` to `0.50`.
- The true `B` of those same chains *falls*. So `Φ_3` is loose on them, and its maximisers are not near-Følner.

*Global four-point bound* `sup Φ_4` over order-3 bin chains (`opt4.out`). It is tighter than `Φ_3` at
every `N`:

| N | 3 | 4 | 5 |
|---|---|---|---|
| sup Φ_4 | 0.953389 | 0.955400 | 0.956702 |

*Local problem* `sup Ψ` over increment chains on `{−L..L}` (`opt_local.out` for general kernels,
`opt_localsym.out` for mirror-symmetric kernels, which strips realise):

| L | 1 | 2 | 4 | 8 | 16 |
|---|---|---|---|---|---|
| general | 0.946825 | 0.957130 | 0.965728 | 0.970840 | 0.973539 |
| symmetric | 0.942809 | 0.951363 | 0.960860 | 0.965187 | 0.966919 |

- At `L = 1` the symmetric optimum is exactly the product value `2√2/3`.
- The general `L = 8` optimum has drift about `0`, a symmetric marginal `g`, and lag-1 increment
  correlation about `−0.52`. So the best local laws are *anti-persistent* walks: a step up is usually
  followed by a step down.
- The gains per doubling of `L` are `0.0103, 0.0086, 0.0051, 0.0027` (general) and
  `0.0086, 0.0095, 0.0043, 0.0017` (symmetric). The `L = 16` values come from the first start only.

*Reading.*
- **Local.** The gains per doubling shrink geometrically, and the ratio itself falls: about `0.6`, then
  `0.53` (general), and about `0.4` (symmetric). Geometric extrapolation puts the general `sup Ψ` near
  `0.977` and the symmetric one near `0.968`.
- **Global.** The `Φ_3` sequence fits `0.982 − 0.0435/√N`. That fit, made from `N ≤ 8`, predicts `0.9694`
  at `N = 12`, against `0.969043` observed. The `N = 16` run and the `Φ_4` run at `N = 6` were stopped
  for time.
- **Together.** The numerics agree on a ceiling of about `0.975–0.985`, well below `1`. Neither is a proof: a slow
multi-scale drift could keep adding gains. That is exactly the open prerequisite (P1).

## Verdict for the size-only programme

- **Proved.** Near-Følner behaviour in (E2) needs rank-locality at rate `δ ≤ 1.972 √(1 − B)`, for every
  stationary law. So every candidate with a macroscopic rank step is dead, whatever its memory, hidden
  types or hierarchy. For example, any law whose neighbours have independent ranks (census type) has
  `δ = 1/3`, and so `B ≤ 0.9714`.
- **Decomposed.** To prove a ceiling `< 1` for every size-only split law, it suffices to prove (P1)
  (`sup Ψ < 1`) together with (P2) (localisation: as `δ → 0`, the global `sup Φ_3` is at most the local
  `sup Ψ`, which the strip check supports). Each can fail on its own.
  - A counterexample to (P1) would be an anti-persistent multi-scale increment law with `Ψ → 1`.
  - A failure of (P2) would need a non-local rank-local law, one that beats the local optimum through
    varying drift.
  - Laws that escape part 4 altogether form (P3): their splits read hidden types or neighbours.
- **Evidence.** The numerics put `sup Ψ` and `sup Φ_3` at about `0.975–0.985`. If (P1) and (P2) hold,
  size-only split laws are capped at about `0.98` for every memory depth, and the programme has to move
  to (P3). There, only `B ≤ E√S` and part 3 are available, and part 3 is vacuous in the rank-local regime.
- **Next step.** Prove `sup Ψ < 1`. The route is to quantify valley-deletion non-invariance: bound the
  Hellinger defect between `h(s | a, m)` and `g(m−s) g(a−m)`, uniformly over increment laws.

**Artifacts** (all in `experiments/thompson-f-three-point-scale-2026-09-17/`):

| Script | Checks, and output file |
|---|---|
| `three_point_bound.py` | `check`: `Φ_3 = B` on order-1 chains to `5e-11`; the product value `2√2/3` (`three_point_check.out`) |
| `four_point_bound.py` | `check`: lossless on order-1 chains; `Φ_4 ≥ B` on order-2 chains; `Φ_4 ≤ Φ_3` (`four_point_check.out`) |
| `rank_locality_check.py` | exact bin-model check of `Cov(S,V) = δ/2`, `Var S ≥ 3δ^2`, `Φ_3 ≤ 1 − Var S/C` (`rank_locality_check.out`, ALL OK) |
| `local_problem.py` | `check`: the strip realises `Ψ` (`local_check.out`) |

The optimisation logs are `opt_small.out`, `opt_mid.out`, `opt4.out`, `opt_local.out` and `opt_localsym.out`.
