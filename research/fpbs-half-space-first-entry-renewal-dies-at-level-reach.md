---
rg: 2
id: fpbs-half-space-first-entry-renewal-dies-at-level-reach
kind: claim
title: Half-space first-entry renewal along a homomorphism to Z dies at the level-reach floor theta, and every Holder closing of it needs a slab l^q input that alone gives p_c < p_u
distinct_from:
  fpbs-layer-renewal-along-homomorphism-is-critical-l2: that kills renewal with full-band coefficients, scalar via the co-amenable kernel and operator via critical l2, and leaves the half-space-restricted coefficients as its survivor; this kills that survivor, scalar via the level-reach lemma and operator via the slab factor, with no half-space Grimmett-Marstrand input.
  fpbs-no-infinite-cluster-bounded-in-height: that is the pathwise lemma (no infinite cluster bounded in height); this is the class kill built on it.
  fpbs-orbit-uniform-half-tilt-bounds-connectivity-operator: that kills boundary-cocycle tilts bounded uniformly on an orbit; this kills first-entry renewal in the height of a homomorphism, including all character tilts, and leaves weights that are not comparable to a character on the first-entry band.
  fpbs-two-point-lq-threshold-gap-universal: that asks for full-space l^q summability of tau_p above p_c; the slab condition here sums over a height slab only, is weaker, and is shown to be the exact extra input of the operator half-space route.
artifacts:
  - research/fpbs-half-space-first-entry-renewal-dies-at-level-reach-proof.md
---

**ESTABLISHED (class kill).** Proof route:
`fpbs-half-space-first-entry-renewal-dies-at-level-reach-proof`, which uses
`fpbs-no-infinite-cluster-bounded-in-height`.

**Setting.**
- The setting is that of `fpbs-layer-renewal-along-homomorphism-is-critical-l2`.
  `Gamma` is nonamenable, `G = Cay(Gamma,S)`, `h : Gamma -> Z` is surjective,
  and `K = max_S |h(s)|`.
- `U_n = {h >= n}` and `L_n = {h < n}`.
- For `x` and `n >= 1`, the **first-entry set** is
  `FE_n(x) = { z in x U_n : some open path from x to z has every vertex except z in x L_n }`.
  Here `x U_n = {h >= h(x) + n}`.
- The **half-space coefficient** is `G(n) = E_p |FE_n(o)|`, and its character
  tilts are `G_mu(n) = E_p sum_(z in FE_n(o)) e^(mu h(z))` for `mu in R`.
  In the notation of the full-band node, `beta^hs_j = G(jK)`.
- For `J >= K`, the **first-entry kernel** is `Q_J(x,y) = P_p(y in FE_J(x))`,
  and the **slab kernel** is `T^J(x,y) = tau_p(x,y) 1{-K < h(y)-h(x) < J}`.
- The slab `l^q` sum is `kappa_q(p) = sum_(h(y)=0) tau_p(o,y)^q`. By
  Harris–FKG along one generator `s` with `h(s) != 0`, it is finite iff the
  same sum over any slab of finite width is finite.

**Theorem.** Let `p > p_c(G)`, so that `theta(p) > 0`.

1. **Renewal (BK at the first entry).** For `n >= 1` and `m >= K`,
   ```text
   G_mu(n+m) <= G_mu(n) max_(m-K < m' <= m) G_mu(m')      (every mu in R, mu = 0 is G).
   ```
   The same inequality holds with `e^(mu h)` replaced by any submultiplicative
   weight. Pointwise, for every `J >= K`,
   ```text
   tau_p(x,z) <= sum_(k >= (H-J)/(J+K)) (Q_J^k T^J)(x,z),   where H = h(z)-h(x) >= 0.
   ```
2. **Level-reach floor.** `G(n) >= P_p(o <-> U_n) >= theta(p)` for every
   `n >= 1`. Also, for every `mu`,
   `G_mu(n) >= theta(p) e^(mu n) min(1, e^(mu(K-1)))`.
3. **Half-space percolation gives infinity.** If the lower half-space
   percolates from `o`, meaning `P_p(o` lies in an infinite component of the
   open subgraph induced on `L_n) > 0`, then `G(n) = infinity`.
4. **Scalar kill.** For every `n >= 1` and every `mu in R`:
   ```text
   G(n) >= 1,        G_mu(n) >= e^(mu n) min(1, e^(mu(K-1))).
   ```
   In particular `max_(m-K < m' <= m) G_mu(m') >= e^(mu m) min(1, e^(mu(K-1)))`
   for every window, and `G_w(n) >= 1` for every weight `w >= 1`.

   So no closing condition of the scalar half-space renewal holds at any
   `p > p_c`. This covers every window, every band width, every character
   tilt, and every weight `w >= 1`. The step where every member dies is the
   iteration of a single first-entry step `k` times, which gives
   `theta(p) <= P_p(o <-> U_N) <= G(J)^k` for all large `N`. That is
   incompatible with a coefficient below `1`.
5. **Hölder closings are inert for the flagship.** Close the pointwise chain
   of item 1 by a dual pair `(l^(q'), l^q)`, `1 <= q <= infinity`:
   ```text
   tau_p(o,z) <= sum_(k >= k_0(h(z))) ||Q_J||_(q'->q')^k ||T^J delta_z||_q .
   ```
   Here `Q_J` acts on row vectors, `nu -> nu Q_J`, and the norm is that of
   this action on `l^(q')`.
   - For `q = infinity`, the coefficient is `||Q_J||_(1->1) = G(J) >= 1`.
     That is scalar, and it dies by item 4.
   - For `q < infinity`, the route needs `||Q_J||_(q'->q') < 1` for some `J`, together with
     `kappa_q(p) < infinity`. But `kappa_q(p) < infinity` at a single
     `p > p_c` already gives `p_c < p <= p_u`, with no renewal. The reason is
     that for `p > p_u`, `tau_p >= theta^2` on the infinite slab.

   So the operator half-space route adds nothing toward
   `fpbs-benjamini-schramm-universal`. Its only non-renewal input is a slab
   `l^q` bound, which is sufficient for `p_c < p_u` by itself.

**Consequence for the height-renewal family.** Combined with
`fpbs-layer-renewal-along-homomorphism-is-critical-l2`, every BK renewal in
the height of a homomorphism `Gamma -> Z` falls into one of four cases, on
every group with infinite abelianization and every Cayley graph:
- scalar full-band: dies at "coefficient finite";
- scalar half-space, including character tilts: dies at "coefficient
  `< 1`", by the level-reach floor;
- operator full-band: needs critical `l^2`;
- operator half-space: needs a slab `l^q` bound, which already implies
  `p_c < p_u`.

So none of them reduces the flagship to anything weaker than an input that
proves it directly. In particular, the half-space Grimmett–Marstrand
statement named as the survivor's gate is **not needed**. Item 2 is
unconditional.

**Calibration.** On `T_4` with `h(a) = 1` and `h(b) = 0`:
- `G(n) = infinity` for `p > 1/3`, consistent with items 2–4. The lower
  half-space percolates there. It contains subdivided `N_L`-ary trees, with
  every edge a path of length `L` and `N_L^(1/L) -> 3`.
- The `q = 2` route runs exactly on `(1/3, 1/sqrt 3)`, where
  `1/sqrt 3 = p_(2->2)`:
  - `kappa_2(p) = sum_(h(y)=0) p^(2|y|)` is finite iff `3p^2 < 1`, since
    height-zero reduced words number `3^n n^(-1/2)` up to constants;
  - for `p < 1/sqrt 3`, Haagerup's inequality gives
    `||Q_J||_(2->2) <= sum_(n>=J) (n+1) p^n (4 3^(n-1))^(1/2) -> 0` as
    `J -> infinity`.

  Its slab input alone certifies `p_c < p_u` there.

**What is not claimed.**
- Weights that are not comparable to a character on the first-entry bands
  are not covered by item 4. An example is a weight concentrated near the
  line `<z>`. This is boundary-tilt territory, see
  `fpbs-orbit-uniform-half-tilt-bounds-connectivity-operator`.
- Whether `kappa_q(p) < infinity` for some `p > p_c` and some `q < infinity`
  is not decided. It is a weakening of `fpbs-two-point-lq-threshold-gap-universal`
  to a slab, and it implies the flagship on the graph.
- Whether `G(n) = infinity` for every `p > p_c`, without half-space
  percolation, is not decided. It is not needed for the kill.
- The operator route is not claimed to be useless for the stronger target
  `fpbs-relative-gap-along-every-amenable-subgroup-universal`. When its two
  inputs hold, it gives exponential decay of `tau_p(o,z^n)` for
  `h(z) != 0`, which is the relative gap along `<z>`. What is claimed is that
  its slab input already settles the flagship on the graph.

## Attempts
