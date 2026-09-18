---
rg: 2
id: brin-thompson-nv-sum-type-size-functions-are-not-cnd
kind: claim
title: "For n >= 2 no size function of nV that is asymptotically l^p-like on disjoint-support baker maps is cnd, for any finite p: 2^d disjoint pieces cost only 3d+1 letters, so every cnd function is capped at O((log aggregate)^2); with the max-type kill this closes the whole l^p family, 1 <= p <= infinity"
distinct_from:
  brin-thompson-nv-max-type-size-functions-are-not-cnd: that kills the sup over the pieces (p = infinity) on a fixed Z^3 of three disjoint baker maps, by an l^inf certificate and a scaling limit, and explicitly leaves untouched the functions that are additive over disjoint supports; this kills exactly those, for every finite p, and the mechanism is word-length compression of the number of pieces rather than the shape of the norm
  brin-thompson-2v-brick-count-is-exponentially-distorted: that is the group-theoretic input (an explicit length-(3d+1) word equal to a product of 2^d disjoint-support baker maps, with L = 2^(d+1)); this is its consequence for conditionally negative definite functions
  nv-local-density-walls-bounded-on-callard-salo-element: that kills Lebesgue-integrated fibrewise functions with subexponential germ weights, on the Callard--Salo element, and depends on an open dynamical input; this kills counting aggregates over diagram pieces, needs no dynamical input, and does not reach measure-weighted integrals, which weight each of the 2^d pieces of B_d by 2^(-d)
  nv-vertically-triangular-chart-cocycles-are-bounded: that bounds l^2 cocycles supported on vertically triangular charts, by a paradoxicality argument on three elements of V x id; this bounds every cnd function, of whatever origin, along one explicit compressible family, and is a growth ceiling rather than a boundedness statement
  nv-cnd-functions-grow-at-most-linearly-along-fibre-elements: that is a linear ceiling in the power k along elements fixing a coordinate; this is a quadratic ceiling in the word length along a family whose piece count is exponential, and B_d fixes no coordinate
artifacts:
  - experiments/brin-thompson-cnd-2026-09-18/brick_compression.py
  - experiments/brin-thompson-cnd-2026-09-18/lp_certificates.py
  - experiments/brin-thompson-cnd-2026-09-18/lp_certificates.json
---

**ESTABLISHED** by `brin-thompson-nv-sum-type-size-functions-are-not-cnd-proof`.

## Setting

Notation is that of `brin-thompson-2v-brick-count-is-exponentially-distorted`: `n >= 2`, `beta` the
global baker map of `2V <= nV`, `tau = id x rho`, `b_w` the baker map supported on `[w] x C`,
`B_d = prod_{|w| = d} b_w`, `T_d = beta^{-d}(sigma x id)beta^d`, and `c` the exponent cocycle with
kernel `K = union_m K_m`.

A function `psi: nV -> R` is **conditionally negative definite (cnd)** if it is symmetric
(`psi(g^{-1}) = psi(g)`) and `sum_{i,j} c_i c_j psi(g_i^{-1} g_j) <= 0` whenever `sum_i c_i = 0`.
Adding a constant preserves cnd, and `Psi = psi + M(1 - delta_e)` is the normalisation used in
`brin-thompson-nv-max-type-size-functions-are-not-cnd`.

For a finite **antichain** `S` of binary words (no one a prefix of another) and integers
`k = (k_w)_{w in S}`, the maps `b_w`, `w in S`, have pairwise disjoint supports, so
`g(S,k) = prod_{w in S} b_w^{k_w}` is well defined, and `(S,k) |-> g(S,k)` is injective on
`{k_w != 0}`. For `1 <= p < infinity` write the **`l^p` aggregate**

  `A_p(S,k) = ( sum_{w in S} |k_w|^p )^{1/p}`,   `A_infinity(S,k) = max_w |k_w|`.

`A_1` is the sum-type (additive over disjoint supports) aggregate; `A_infinity` is the max-type one
studied in `brin-thompson-nv-max-type-size-functions-are-not-cnd`.

## Statement

1. **(quadratic ceiling)** Let `Psi` be cnd on `nV`, and `K_0 = max(Psi(beta), Psi(tau)) - Psi(e)`.
   Then for all `d >= 0`
   `Psi(B_d) <= Psi(e) + (3d+1)^2 K_0` and `Psi(T_d) <= Psi(e) + (2d+1)^2 K_1`,
   with `K_1 = max(Psi(beta), Psi(sigma x id)) - Psi(e)`.
2. **(every finite `p` dies)** Fix `1 <= p < infinity`. Suppose `Psi` is cnd on `nV` and
   `F: [1, infinity) -> R` is nondecreasing with `Psi(g(S,k)) >= F(A_p(S,k))` for every antichain
   `S` and every `k`. Then
   `F(t) <= Psi(e) + (3 p log_2 t + 1)^2 K_0` for every `t` of the form `2^{d/p}`,
   and hence `F(t) = O_p((log t)^2)`.
   In particular there is **no** cnd `psi` on `nV`, and no `M`, with
   `psi + M(1 - delta_e) >= F(A_p)` for an `F` growing faster than `(log t)^2`; and no cnd
   `psi` with `psi(g(S,k)) / G(A_p(S,k)) -> kappa > 0` for a `G` that is regularly varying of
   positive index.
3. **(three pieces already kill `p > 2`)** On the fixed `Z^3` of `b_00, b_01, b_1` the aggregate is
   the `l^p` norm of `(m,q,r) in Z^3`. For each `p` in the certified list
   `{2.15, 2.25, 2.5, 3, 4, 6, 10}` there is an explicit integer zero-sum vector on a grid
   `{-k..k}^3` with `sum c_x c_y ||x - y||_p > 0`, so `||x - y||_p` is not cnd on `Z^3`; by the
   Schoenberg power step (Step 4 of
   `brin-thompson-nv-max-type-size-functions-are-not-cnd-proof`), `||x - y||_p^gamma` is not cnd for
   any `gamma >= 1`. Consequently, for those `p`, no cnd `Psi` on `nV` has
   `Psi(g(S,k)) / G(||k||_p) -> kappa > 0` on the antichain `S = {00, 01, 1}` for a `G` regularly
   varying of index `gamma >= 1` — three pieces already suffice, no growth in the piece count
   needed. For `p <= 2` no such certificate exists and none can: `l_p^3` embeds
   isometrically in `L^1` for `1 <= p <= 2`, so `||x - y||_p` is cnd there. So on three pieces the
   surviving exponents are exactly `p <= 2`; item 2 removes those too, once the number of pieces is
   allowed to grow.
4. **(the cocycle kernel, P3)** Let `Psi` be cnd on `nV` and `F` nondecreasing with
   `Psi(k) >= F(#{level-m cubes moved by k})` for `k in K_m`. Then `F(N) = O((log N)^2)`: `T_d` lies
   in `K_{d+1}`, moves all `2^{n(d+1)}` cubes of that level, and has `|T_d| <= 2d+1`. So the natural
   locally finite candidate for prerequisite P3 (`brin-thompson-nv-cnd-proper-on-cocycle-kernel`) —
   the Hamming length `#moved` of the permutation, which is cnd and proper on each `Sym(N)` — cannot
   be dominated by any cnd function of `nV` beyond `(log N)^2`.
5. **(the closed family)** Combining with `brin-thompson-nv-max-type-size-functions-are-not-cnd`:
   for every `p in [1, infinity]`, no cnd function of `nV` is asymptotically `G(A_p)` with `G`
   regularly varying of positive index (index `>= 1/4` is needed only for `p = infinity`, which is
   the case handled there). The `l^p` family of aggregates over disjoint-support pieces is dead.

## Where every member dies, and the invariant

- **Invariant:** the number of pairwise disjoint-support conjugate baker pieces that a word of
  length `l` can contain. In `V = 1V` it is `O(l)` (refinement of trees is subadditive, item 6 of
  `brin-thompson-2v-brick-count-is-exponentially-distorted`); in `nV`, `n >= 2`, it is `2^{Omega(l)}`
  (refinement of brick partitions is a grid).
- **Death step:** `sqrt(Psi - Psi(e))` is subadditive for every cnd `Psi`, so `Psi` grows at most
  quadratically in word length, while a `p`-aggregate over the pieces of `B_d` grows like `2^{d/p}`.
  Every member of the class dies at `d ~ 3 p log_2 t`.

## What survives

- **Measure-weighted (integrated) functions.** `B_d` has `2^d` pieces, but each has measure `2^{-d}`,
  so `int Phi(r(B_d, x)) h(x) dlambda(x) = Phi(Theta(d)) ||h||_1` is polynomial in `d` and the
  ceiling is not violated. These are the class killed instead by
  `nv-local-density-walls-bounded-on-callard-salo-element` (conditional on
  `callard-salo-element-is-ae-locally-periodic`). The two obstructions are complementary: counting
  aggregates die here, Lebesgue-weighted aggregates die there. A surviving fibrewise candidate must
  weight pieces strictly between counting and Lebesgue — exponentially in germ size, and still with
  total weight `O(d^2)` on the level-`d` partition.
- **Very slow aggregates.** `F(t) = (log t)^{gamma}` with `gamma <= 2` is not excluded by item 2; on
  `B_d` these give `d^{gamma}`. But on the `Z^3` of item 3, `(log A_1)^{gamma}` is a slowly varying
  function of an `l^1` norm, which is cnd, so nothing kills them yet. Note `log L` itself is at the
  ceiling: `log_2 L(B_d) = d + 1` and `(log L)^{gamma}` gives `d^{gamma}`; `log L` dies for the other
  reason, because it is the `l^inf` norm on the `Z^3`.
- **Non-aggregate constructions**: functions that are not built from the diagram of `g` at all,
  e.g. from a representation with no chart model.

## Attempts (this node)

- **2026-09-18 (e2-w2-nv-cnd-beyond-max).** The statement above, established. The falsifiable first
  step was the identity `beta B_d beta^{-1} = tau B_{d-1}`, checked exactly for `d <= 8` before
  anything was claimed.
- **Not obtained: `0 < beta < 1/4` for the max-type case.** The residual gap left by
  `brin-thompson-nv-max-type-size-functions-are-not-cnd` (item "Not claimed") is untouched here.
  A Misiewicz-type theorem (a positive definite function of `||x||_infinity` on `R^3` is constant)
  would close it; the `l^p` certificates of item 3 show the same pattern — the grid needed grows as
  the exponent decreases, `k = 2` at `p = 2.5` and `k = 5` at `p = 2.15` — so a brute-force search
  is not the route.
