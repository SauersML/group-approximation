---
rg: 2
id: thompson-f-iid-forest-test-vectors-are-bounded-below-one
kind: claim
title: Every product-form (i.i.d. tree) test vector on pointed-forest windows of Thompson's F has limiting Rayleigh quotient at most 1 - 1/1280
distinct_from:
  thompson-f-norm-bound-from-forest-renewal-test-vector: that certifies a lower bound ||P|| > 0.9397 with one member of this family; this proves an upper bound 1 - 1/1280 on what any member of the family can certify as the window grows, which settles negatively the proxy "sup_N of the ansatz optimum is 1" left open there and in the root.
  f-invariant-means-on-the-free-magma-are-never-products: that is qualitative and about exact finitely additive means on the free magma; this is quantitative, about l^2 test vectors in the Cayley graph of F, and gives a uniform spectral gap from the product structure.
  free-binary-systems-carry-no-idempotent-mean: that rules out exact idempotent means; this proves a quantitative Hellinger bound H(nu, nu*nu) >= 1/8 for probability laws on the positive integers and turns it into a Rayleigh-quotient ceiling.
  thompson-f-cnd-certificates-need-near-exponential-ball-growth: that constrains conditionally negative definite certificates by ball growth; this constrains positive-side Rayleigh certificates by the product structure of the test vector.
  thompson-f-is-amenable: the root is untouched; this closes one explicit numerical route toward it.
artifacts:
  - experiments/thompson-f-iid-forest-gap-2026-09-17/gap_audit.py
  - experiments/thompson-f-iid-forest-gap-2026-09-17/gap_audit.out
  - experiments/thompson-f-iid-forest-gap-2026-09-17/idempotence_scout.py
  - experiments/thompson-f-iid-forest-gap-2026-09-17/idempotence_scout.out
---

**ESTABLISHED (direct proof, unrefereed).**

*Setting.* This uses the notation of `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`, steps 1 to 5.
- `P` is the simple random walk operator of `F = <s_0, s_1>` on `l^2(F)`, and `K = 4P`.
- `S_n` is the set of pointed forest windows with `n` leaves in total, and `E : S_n -> F` is the injective embedding
  in which the four moves (pointer right/left, merge/split) are Cayley edges.
- A **product-form test vector** is given by two real functions `x, y` on finite binary trees, both finitely
  supported (a tree-size cutoff `N`), with `x(leaf) != 0`. It is
  `f_n(E(T_0, ..., T_{m-1}; i)) = y(T_i) prod_{j != i} x(T_j)` on `E(S_n)`, and `0` off `E(S_n)`.

This covers every vector of that route and of `split_ansatz.py`, for every `N`. There `x` is multiplicative with
arbitrary split weights `phi`, and `y` has the special form `g * y(L) x(R)`. Here `x` and `y` are arbitrary.

**Theorem.**
- (a) **Limit formula.** `lim_n <f_n, P f_n> / <f_n, f_n>` exists and equals `(b^2 + m)/2`. This is computed after
  a tilt `x -> r^{|T|/2} x`, `y -> r^{|T|/2} y`, which changes no Rayleigh quotient and makes
  `u = x / ||x||` with `sum_T u(T)^2 = 1`. Normalize `y` to unit length and set
  - `b = <u, y>`;
  - `m = <J(y (x) u), y>`, where `J : l^2(trees x trees) -> l^2(trees)` is the isometry `(S, U) -> (S, U)`
    onto non-leaf trees.
- (b) **Uniform ceiling.** For all unit vectors `u, y` in `l^2(trees)`, `(b^2 + m)/2 <= 1 - 1/1280`.
- Hence no product-form test vector, with any cutoff `N` and any weights, has limiting Rayleigh quotient above
  `1 - 1/1280 = 0.99921875`. In particular `sup_N` of the ansatz optimum of
  `thompson-f-norm-bound-from-forest-renewal-test-vector` is at most `1 - 1/1280`. That optimum was
  `0.8777, 0.9118, 0.9290, 0.9400` at `N = 9, 20, 40, 80`, so the "computable proxy" in the root's Attempts is
  **false**: this family cannot approach `1`, whatever the tree-size law does as `N -> infinity`.

**Class killed.** Every Rayleigh certificate for `||P|| -> 1` that is built on pointed-forest windows with
independent trees, that is, windows weighted by an i.i.d. (Galton–Watson-like) tree law with any pointer-tree weight.
- *Invariant:* **additive idempotence of the bulk tree-size law.** Let `nu` be the law of `|T|` under `pi = u^2`.
  A near-eigenvector would need `nu ≈ nu * nu`. But for every probability law on the positive integers,
  `Hellinger(nu, nu*nu) >= sup_t |phi_nu(t) - phi_nu(t)^2| / 2 >= 1/8`.
- *Where every member dies:* at the **merge move** `s_1`. That edge compares the pointer tree `(S, U)` with the pair
  `S, U` of adjacent trees. Independence makes the law of that pair a product, so the size of the merged tree has
  law `nu * nu`, while stationarity requires law `nu`. The ceiling
  `2 epsilon_1 + epsilon_2 >= 1/8` follows, with
  - `epsilon_1 = ||y - u||`, the pointer defect;
  - `epsilon_2 = ||J(y (x) u) - y||`, the merge defect.
- *Numbers.* `gap_audit.py` evaluates every term of the chain on the certified parameters (`gap_audit.out`):
  - at `N = 80`: `(b^2+m)/2 = 0.940020`, `2 eps_1 + eps_2 = 0.674`, `H_tree = 0.521`, `H_size = 0.517`,
    `sup|phi - phi^2|/2 = 0.225`;
  - at `N = 40`: the corresponding values are `0.928967`, `0.730`, `0.566`, `0.562` and `0.251`.

  So the merge defect `eps_2 ≈ 0.47` is what holds the optimizer down.
- *Sharpness of the invariant (float scouting, not a certificate).* `idempotence_scout.py` minimizes
  `H^2(nu, nu*nu)` over laws on `{1..M}`: `0.294, 0.224, 0.188, 0.167` at `M = 50, 200, 800, 3200`. The log-uniform
  family has limit `2 - 4 sqrt(2)/3 ≈ 0.114`. So the true floor of `H` lies between `1/8` and about `0.34`, and the
  constant `1/1280` is not sharp. The true ceiling of the family is plausibly near `0.99`.

**Scope and survivors.**
- This is a statement about `n -> infinity` at fixed weights. At a fixed finite `n` the merged size is determined by
  the rest of the window, and no uniform-in-`n` bound is claimed.
- What survives is test vectors in which **neighbouring tree sizes are correlated**: Markov-chain forest laws,
  hierarchical or multi-scale weights (such as Moore's Følner-type sets), and vectors that are not of product form
  across the window. Any such route must break the product structure at the merge move.
- The theorem says nothing about `||P||` itself. The root stays open.

Proof: route `thompson-f-iid-forest-test-vectors-are-bounded-below-one-proof`.

## Attempts

- **2026-09-19 (swarm-0917-w14-w14-f-last1, entropy-measure, obstruction).** Opened to settle the proxy
  "`sup_N` of the ansatz optimum is `1`" left in the root under "Explicit spectral test vectors". It is settled
  negatively by the Hellinger idempotence gap.
  - Not attempted: Markov-correlated forest laws. The limit formula for those is a transfer-operator top eigenvalue,
    and the idempotence obstruction does not apply to them directly.
