---
rg: 2
id: thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit
kind: claim
title: Stationary Markov size-chain test vectors for Thompson's F saturate near Rayleigh value 0.977 in the log-scale limit, below the product cap 71/72
distinct_from:
  thompson-f-norm-bound-from-forest-renewal-test-vector: that certifies ||P|| > 0.9397 with one product-form vector on finite windows; this studies the correlated (Markov-in-size) family in infinite volume and in the log-scale limit, and certifies nothing about ||P||.
  thompson-f-is-amenable: that is the root; this only bounds (numerically) one family of test vectors for ||P|| = 1 and decides nothing.
artifacts:
  - experiments/thompson-f-markov-forest-2026-09-17/markov_ansatz.py
  - experiments/thompson-f-markov-forest-2026-09-17/scale_limit.py
  - experiments/thompson-f-markov-forest-2026-09-17/scale_limit_order2.py
  - experiments/thompson-f-markov-forest-2026-09-17/lift_check.py
  - experiments/thompson-f-markov-forest-2026-09-17/lift_check.out
  - experiments/thompson-f-markov-forest-2026-09-17/lift_fast.out
  - experiments/thompson-f-markov-forest-2026-09-17/lift_fast_big.out
  - experiments/thompson-f-markov-forest-2026-09-17/runs.out
  - experiments/thompson-f-multitype-forest-2026-09-17/multitype_scale.py
  - experiments/thompson-f-multitype-forest-2026-09-17/selftest.out
  - experiments/thompson-f-multitype-forest-2026-09-17/runs.out
---

**OPEN** (numerical evidence plus exact reductions; no rigorous ceiling).

**Claim.** Test vectors of the following kind cannot push Kesten's Rayleigh quotient for `F` to 1:
- sizes of neighbouring trees form a stationary Markov chain of finite order (orders 1 and 2 tested);
- shapes are recursive given sizes.

In the log-scale limit their supremum is `R* ≈ 0.977`. That is above the product value
`1/2 + √2/3 = 0.9714`, but it is well below 1 and below the product cap `71/72`.

**Setting.** This is the pointed-forest model of `thompson-f-norm-bound-from-forest-renewal-test-vector`:
- trees `…, T_{-1}, T_0, T_1, …`, with the pointer at `T_0`;
- `x_0` moves the pointer;
- `x_1` merges `T_0` and `T_1` into `(T_0, T_1)`.

For a law `Q` of configurations and `u = √Q`, the Rayleigh quotient is `(BC_shift + BC_merge)/2`. Here
`BC` is the Bhattacharyya (Hellinger) affinity.

**Established pieces.** (E1) and (E3) are exact derivations, each short. (E2) is a formal limit.

*(E1) Markov formula in infinite volume.* Take the following law `Q`:
- the sizes `n_j` form a stationary chain with kernel `K` on `{1..M}` and stationary law `π`;
- given the sizes, the trees are independent, with law `w(T) = κ(|L| | |T|) w(L) w(R)`.

Then `BC_shift = 1`. Set `S = √K`, `G = Sᵀ diag(π) S` and `H = S Sᵀ`, and
```
BC_merge = Σ_m ( Σ_{k<m} β_k(m) √κ(k|m) ),     β_k(m) = G(k,m) S(k,m−k) H(m−k,m).
```
The optimum over `κ` is `κ(k|m) ∝ β_k(m)²`, and it gives `BC_merge = Σ_m ( Σ_k β_k(m)² )^{1/2}`.

Derivation. Compare `Q` at a merged configuration `(…, a, m, l, …)`, where the top split is `(k, m−k)`,
with `Q` at the unmerged configuration `(…, a, k, m−k, l, …)`:
- the factors left of `a` and right of `l` cancel;
- summing over `l` gives `H`;
- summing over `a` gives `G`.

For product kernels `K(a,·) = p` this reduces to `BC(p, p∗p)`, as in `thompson-f-norm-bound-from-forest-renewal-test-vector`.

*(E2) Log-scale limit* (a formal limit; `M → ∞` is not justified rigorously here). Put `y = log n / log M ∈ [0,1]` and let `M → ∞`, with densities `f_a(·)` on the
`y`-scale. Then:
- merge acts as `max` on `y`;
- a split of rescaled size `m` has one child of size `m` and one child of size `s ≤ m`, on the left or the
  right.

With `r_m` the reversed row, `J(a,b) = π(a) f_a(b)`, `U(m) = P(y_{-1} < m | y_0 = m)` and
`D(m) = P(y_1 < m | y_0 = m)`:
```
B = ∫_0^1 dm √π(m) · ( ∫_0^m [ J(s,m) BC(r_s,r_m)² + J(m,s) BC(f_s,f_m)² ] ds )^{1/2}.
```
The first term is the case where the left child is small, the second where the right child is small.

- For a product kernel (`f_a = π` for every `a`), `B = ∫ π √(2Π) = 2√2/3` exactly, **for every law `π`**.
  This is the harmonic value of the product case, and in the scale limit no product law can beat it.
- For kernels that are piecewise constant on `N` bins, the formula is exactly a finite sum
  (`scale_limit.py`). The code checks the product identity and the order-2 embedding to about `1e-16`.

*(E3) Necessary conditions for B → 1* (from `BC² ≤ 1 − TV²` and Jensen). They follow from
`B ≤ ∫ π √(U+D)` and `∫ π (U+D) = 1`:
```
B² ≤ 1 − E[ 1{up} TV(r_{y_0}, r_{y_1})² ] − E[ 1{down} TV(f_{y_0}, f_{y_1})² ],     B ≤ ∫ π √(U+D).
```
So `B → 1` needs all three of the following:
- along up-steps, the reversed rows become equal;
- along down-steps, the forward rows become equal;
- `U + D → 1` in `L¹(π)`.

A chain whose up-steps connect its states and whose reversed rows are all equal is a product chain. The
product has `U = D = Π`, so its defect `∫ π √(2Π) = 2√2/3` depends on nothing. This is the mechanism
behind the saturation (a heuristic; it is not made quantitative here).

**Numerical evidence** (float64 L-BFGS from several random starts). All starts agree, with one exception: in order 1 the
widest start (`trial 3`) stays at the product critical point `2√2/3`.
Full logs are in `runs.out`.

| family | resolution | best `B` | `R = (1+B)/2` |
|---|---|---|---|
| product, scale limit | any | `2√2/3 = 0.942809` | `0.971405` |
| order-1 Markov, scale limit | `N = 4, 8, 16, 32` bins | `0.951396, 0.953127, 0.953743, 0.953927` | `0.97696` at `N = 32` |
| order-1, extrapolated | `N → ∞` (ratio of differences about 3) | `≈ 0.9540` | `≈ 0.9770` |
| order-2 Markov, scale limit | `N = 4, 8, 12` bins (`N = 12`: one start) | `0.952351, 0.954274, 0.954781` | `0.97739` at `N = 12` |
| order-2, extrapolated | `N → ∞` | `≈ 0.955` | `≈ 0.9777` |
| order-1, discrete | `M = 20, 40, 80` | `0.81224, 0.84986, 0.87457` | product `0.80785, 0.84425, 0.86791` |

- *Memory barely helps.* Going from order 1 to order 2 at equal resolution gains about `0.001` in `B`.
  Refining the bins converges geometrically.
- *The optimal order-1 kernel* is positively correlated: big trees sit next to big trees. Its stationary
  law is increasing in `y`.
- *Finite sizes are far from the limit* (`lift_check.py`, `lift_fast.out`). Lifting the `N = 8` optimal kernel
  log-uniformly to sizes `1..M`:
  - Markov gives `0.765, 0.812, 0.847, 0.869, 0.886, 0.897`;
  - product gives `0.857, 0.881, 0.896, 0.905, 0.912, 0.916`;
  - both at `M = 10², 3·10², 10³, 3·10³, 10⁴, 3·10⁴`;
  - at `M = 10⁵`, Markov `0.9067` and product `0.9205` (`lift_fast_big.out`). The gap shrinks
    (`0.019` at `3·10⁴`, `0.014` at `10⁵`), consistent with a Markov limit near `0.953` above the product.

  Empirically, convergence looks like `O(1/log M)`. A cubic fit in `1/log M` returns `0.9424` for the
  product, against the exact `0.9428`, and `0.944` for Markov, a noisy fit. At every `M` computed, the
  lifted Markov vectors stay below the lifted product.
- *Consequence (empirical).* At the sizes computed, this family stays far below the product-plus-pointer
  certificate `0.9743` of swarm-0917-w14-w14-f-break:
  - the discrete optimum for `M ≤ 80`;
  - the lifted kernels for `M ≤ 3·10⁴`.

  Its limit is only about `0.977`. The discrete optimum for large `M` was not computed.

**Class (numerically) killed as a route to `||P|| = 1`:** stationary Markov size chains of finite order
with recursive shapes. This is the "size-correlated neighbour vectors" family that
swarm-0917-w14-w14-f-break named as the next family after its product class kill.

- *Invariant.* In the log-scale limit, merge is `max` on rescaled log-size. This is the same `max` defect
  that fixes every product law at `2√2/3`, independent of the law (E2).
- *Where it dies.* (E3) forces reversed rows to agree along up-steps and forward rows to agree along
  down-steps. With connected up-steps that collapses the chain to a product, whose Jensen defect is
  law-free.
- *Numerics.* Refinement in bins and one extra order of memory each add `≤ 0.001`, converging to `≈ 0.954`.

**Not covered.**
- The finest scale (log-size steps of order 1) combined with the scale limit.
- Hierarchical or hidden-state laws that encode several log-scales at once. Moore's tower bound suggests
  any Følner-type law must be of this kind.
- Shapes that depend on neighbour sizes.
- Pointer-tilted (non-stationary) laws with `BC_shift < 1`.

## Attempts

- **Scale-limit census of Markov size chains (swarm-0917-w14-w14-f-follow, 2026-09-19, census-computation).**
  - *Done:* derived (E1)–(E3); computed the table.
  - *Dies at:* a rigorous ceiling. Turning (E3) into `sup B < 1` needs a quantitative rigidity statement:
    small TV along up-steps plus `U + D ≈ 1` should force near-product. This is open. The `N`-bin optimum
    is a lower bound for the scale-limit supremum, not an upper bound.
  - *Next falsifiable step:* hierarchical two-level laws, i.e. a Markov chain on increments of log-size
    with its own Markov size chain on top. They test whether the defect decreases level by level (towards
    1) or saturates (as order 1 → 2 suggests).

- **Hidden-state (shape-typed) Markov chains (swarm-0917-w17-w17-f-break, 2026-09-19, census-computation).**
  - *Family.* Every tree carries a state `x = (size, type h ∈ 1..H)`, and the type is a function of the
    shape (a partition of the shapes of each size into `H` classes). The states form a stationary chain `K`.
    A class-`X` tree `(T_0, T_1)` with child states `(x_0, x_1)` has law
    `κ(x_0,x_1|X) σ_{x_0} σ_{x_1} / α(X|x_0,x_1)`. Here `α(·|x_0,x_1)` (with `Σ_X α ≤ 1`) is the fraction
    of child-shape pairs that are assigned to class `X`, and `κ(·|X)` is a probability law.
  - *Formula.* Summing over a part of mass `α` gives `α √(κ/α)`, so (E1) becomes
    `BC_merge = Σ_X ( Σ_{x_0,x_1} β² α )^{1/2}` with the same `β = G S H` on states. With `H = 1` this is
    (E1). The type of the big child may differ from its parent's, so the family can carry level
    counters and other hidden memory that the size chain cannot see.
  - *Code.* `multitype_scale.py` is the (formal, E2-style) scale limit on `N` bins.
    - `selftest.out` checks that `H = 1` reproduces `scale_limit.scale_B` exactly.
    - It checks that a lumped chain (types drawn independently, `α` equal to the type weights)
      reproduces the `H = 1` value to `3e-16`.
    - It checks that `B ≤ 1` on random parameters.
  - *(E3) survives types.* Cauchy–Schwarz gives `G ≤ √(π(x_0)π(X))` and `H ≤ 1`, and `Σ_h α ≤ 1`. Together
    these give `B ≤ E_π √(U + D)` for every hidden-state chain, with `U, D` read off the sizes. So the
    necessary condition `U + D → 1` is unchanged.
  - *Numbers* (`runs.out`, L-BFGS from 1–3 random starts each). The best `B` for each bin count:

    | bins | `H = 1` (from the table above) | `H = 2` | `H = 3` | `H = 4` |
    |---|---|---|---|---|
    | `N = 4` | `0.951396` | `0.952273` | `0.952527` | `0.952622` |
    | `N = 8` | `0.953127` | `0.954217` | `0.954544` | — |
    | `N = 16` | `0.953743` | `0.954756` | — | — |

    - Each extra type adds about 0.3 times what the previous one added: `8.8e-4, 2.5e-4, 1e-4` at
      `N = 4`, and `1.1e-3, 3.3e-4` at `N = 8`. So the values converge in `H`, to about `0.9527`
      (`N = 4`) and `0.9547` (`N = 8`).
    - The whole gain from types is about `0.0013–0.0017`, independent of `N`. That is the same size as
      the order-2 gain.
    - Extrapolating in both `N` and `H` gives `B ≈ 0.9557`, so `R ≈ 0.978`, still below `71/72`.
    - At the optimum, the types are used mainly in the lowest bin, the smallest trees. There is no sign
      of a level-counter mechanism.
  - *Dies at:* the same place as order 2. Hidden memory attached to shapes does not move the saturation,
    so the "hierarchical / hidden-state laws" item of **Not covered** is answered negatively for finite
    `H`, as a formal scale-limit computation.
  - *Still not covered:* ties at leading order (neighbour sizes within a factor `M^{o(1)}`). These are
    invisible to every density kernel in the scale limit, and by (E3) and Moore's tower they are the only
    place left for a size-only law to approach `1`.
  - *Rigorous ceiling:* still open, as before.
- **CDF rigidity ceiling for order 1 (swarm-0917-w17-w17-f-pull, 2026-09-19, probability-random).**
  - *Done* (`thompson-f-markov-size-chain-scale-limit-affinity-at-most-0-978`, ESTABLISHED). This supplies
    the quantitative rigidity statement asked for above. By stationarity and the probability integral
    transform under `r_m`, `E[U(1-D)] - E[U^2]/2` is at most `E[1up TV(r_{y_{-1}}, r_{y_0})]` in absolute value,
    and the same holds for down-steps. Hence `Var(U+D) >= 1/3 - (4/3)·(TV defect)`, with the product chain tight.
  - *Consequence.* Combined with (E3), this proves that every order-1 chain in (E2) has `B <= 0.980656` in
    closed form, and `B <= 0.977125` (`R <= 0.988563`) from a cell-certified Lagrangian dual. So the order-1
    part of this claim's class kill is now proved, within the formal limit.
  - *Still open here.* The numerical value `0.954`, order 2, and finite `M`. At finite `M` merge is a sum and
    the CDF identity fails.
- **Rank-locality and window projections, all memory (swarm-0917-w23-w23-f-break, 2026-09-20, reframing).**
  - *Done* (`thompson-f-scale-limit-merge-affinity-forces-rank-locality`, ESTABLISHED for parts 1–4). For
    every stationary size process with atomless marginal and no ties, `U + D = 1 − c'` a.e. in rank
    coordinates, where `c` is the level down-crossing rate. This uses stationarity only, with no Markov
    property. Hence `Cov(S,V) = δ/2`, `Var S ≥ 3δ^2`, and `B ≤ 1 − 0.257 δ^2`, with `δ = E|V_1 − V_0|`.
    So the rigidity above extends from order 1 to every memory depth, to hidden types and to
    hierarchies. `B → 1` forces rank-local laws.
  - *Size-only split laws.* In addition, `B ≤ Φ_4 ≤ Φ_3 ≤ E√S` for window functionals of the 3- and
    4-point laws, with `Φ_3 = B` exactly on order-1 chains. This removes the order-`k` escape route: one
    finite-dimensional functional covers all orders. The numerics give `sup Φ_3 ≈ 0.969` at `N = 12` bins,
    with an extrapolated limit of about `0.98`.
  - *Where it dies.* In the rank-local regime part 3 is vacuous (`S ≈ 1`). Whether `sup Φ_3 < 1`
    reduces to a translation-invariant local problem `sup Ψ` over increment chains, which is prerequisite
    (P1). Numerically `Ψ ≈ 0.9735` at `L = 16`, with shrinking gains per doubling and an extrapolated limit
    of about `0.977`. The defect comes
    from *valley-deletion non-invariance*: at a local minimum, `g(m−s) = g(a−s)` would be needed, and no
    density satisfies it. A proof of `sup Ψ < 1`, plus localisation (P2), would cap every size-only split
    law at about `0.98`, for every memory depth. Laws whose splits read hidden types or neighbours (P3)
    are outside part 4, and need their own window bound.
