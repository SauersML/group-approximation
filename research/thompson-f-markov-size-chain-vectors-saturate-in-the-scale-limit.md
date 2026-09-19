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
