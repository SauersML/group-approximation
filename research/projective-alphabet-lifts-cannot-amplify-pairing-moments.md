---
rg: 2
id: projective-alphabet-lifts-cannot-amplify-pairing-moments
kind: claim
title: A reduction whose output kernels refine input kernels through a few label projections multiplies the pull-back q-moment by m^((q-2)g/(2q)), so it can make no pairing law smooth
invalidates:
  - finite-moment-hardness-via-projective-amplification
distinct_from:
  pullback-smoothness-needs-exponentially-many-pairings: that lower-bounds the support of one law by about m^n; this is a transfer inequality across a reduction. It lower-bounds the output moment by the input moment times a surplus factor, and it kills reductions whose output support is exponentially large but whose projections are few.
  pair-swap-groups-of-smooth-pairing-designs-contain-alt: that forbids a fixed label structure preserved by every kernel swap; here the output kernels preserve the fibres of p only up to input partner blocks, their swap group can be all of S_2n', and the kill uses the moment inequality, not group orders.
  left-preserving-local-richness-wrappers-are-affine-ug-merges: that covers wrappers that keep the source left alphabet and add right vertices; this covers wrappers that change the left alphabet by projective label maps (padding, product and splitting lifts, projective composition). Its invariant is the surplus g, not the agreement subgroup.
  edge-conjugation-of-2to1-constraints-is-pure-gauge: that is the case g = 0 with p a bijection, where the moment is literally unchanged; this quantifies what happens when the alphabet grows.
artifacts:
  - experiments/projective-amplification-2026-09-17/check_projective_lift_moments.py
  - research/artifacts/unique-games-finite-density-moments-2026-09-12.md
---

**ESTABLISHED.**

## Setting

Fix `m >= 2` and an integer `q >= 1`. For a law `mu` on perfect matchings of
`[2n]`, write `D_mu(z) = m^n Pr_(pi ~ mu)[z constant on every pair of pi]`.
Moments are over the uniform measure, as in
`finite-moment-pairing-2to1-hardness`.

*Projective amplification.* An output left vertex has alphabet
`Sigma' = [2n']` and kernel law `mu'`. Its law is a mixture, with weights
`w_i`, of `k` couplings `(pi, lambda)`. The `i`-th coupling comes with a label
map `p_i : Sigma' -> Sigma_i` of image `S_i`, where `s_i = |S_i|`. Here `pi`
is a kernel at some input left vertex with alphabet `Sigma_i`, and `lambda` is
the output kernel. The **surplus** is `g_i = 2n' - s_i`.

*Compatibility (K).* Every pair `{x,y}` of `lambda` has `p_i(x) = p_i(y)`, or
`{p_i(x), p_i(y)}` in `pi`. Step 0 of the derivation shows that (K) follows
from any per-edge projective soundness relation `p' o phi' = phi o p_i`, the
usual form of a projection-preserving gadget. Padding, product lifts
`Sigma x [r]`, label splitting, and projective composition all satisfy it.

For `z in [m]^(S_i)`, define:

* `D_(S,i)(z) = m^(s_i/2) Pr[z constant on pi|_(S_i) | i]`;
* `E''_i = { z : z o p_i in E' }`;
* `theta_(*,i)`, the infimum over `pi` of `Pr[z o p_i in E']`, for `z` uniform
  among the colourings constant on `pi|_(S_i)`.

`R` is the largest super-block size. A super-block is the `p_i`-fibre of one
point of `S_i`, or of one pair of `pi|_(S_i)`. `W_kappa` is the set of
colourings of `[2n']` in which every colour count is within `kappa sqrt(2n')`
of `2n'/m`.

## Theorem

For every output set `E'` and every `i`:

```text
(T)   ||1_(E') D_(mu')||_q^q >= w_i^q  m^((q-2) g_i / 2)  ||1_(E''_i) D_(S,i)||_q^q
(T1)  ||1_(E') D_(mu')||_q   >= w_i  theta_(*,i)  m^((q-2) g_i / (2q))
(S)   |supp mu'| <= sum_i  #{pi|_(S_i)}  (2n')^(3 g_i / 2)
```

Moreover, if `E'` contains `W_kappa`, then `theta_(*,i) >= 1 - R/kappa^2`.

## Kill

Let `q >= 3`, `E'` contain `W_kappa`, `kappa^2 >= max(2R, 4)`, and
`||1_(E') D_(mu')||_q <= C`. Let `S_in = max_i #{pi|_(S_i)}` count the distinct
restricted input kernels.

* **(K1)** Every map has `w_i <= 2C m^(-(q-2) g_i / (2q))`, so
  `k >= m^((q-2) g_min / (2q)) / (2C)`.
* **(K2)** For every `G >= 0`, at least one of the following holds:
  * `k > m^((q-2) G / (2q)) / (4C)`;
  * `k S_in (2n')^(3G/2) >= (4C)^(-q/(q-1)) m^(n')`.
* **(K3)** In particular
  ```text
  k >= min( m^((q-2) n' / (6q log_m(2n'))) / (4C) ,  (4C)^(-q/(q-1)) m^(n'/2) / S_in ).
  ```
  If the input kernels are polynomially many (Grassmann or affine 2-to-1
  instances), a bounded moment forces `exp(Omega_(q,m,C)(n'/log n'))`
  projection maps per output left vertex.
* **(K4)** A map of weight `w_i` with any surplus forces
  `||1_(E''_i) D_(S,i)||_q <= C / w_i`. So the input kernels, restricted to
  `S_i` and measured on the pulled-back window `E''_i`, must already satisfy
  the bounded-moment condition. With `g_i = 0` and `S_i = Sigma_i` this is
  the input condition itself, since `E''_i` is then a relabelled window. No projective lift
  improves a moment.

**Where every member dies.**

* **Invariant.** The surplus `g_i` together with the number `k` of
  projections.
* **Step.** The lifted-colouring domination
  `D'(z o p) >= m^(n' - s/2) w D_S(z)`. Colourings constant on the coarse input
  kernel lift injectively, and they are over-represented by the factor
  `m^(g/2)` relative to their uniform mass. For `q > 2` the power count turns
  this into `m^((q-2)g/(2q))`.
* **Consequence.**
  * Bounded surplus gives no amplification (K4).
  * Unbounded surplus makes the moment blow up (K1).
  * Mixing a few maps with small and large surplus hits the entropy bound
    through the support count (K2, K3).

The exact demo in the artifact takes the fully rich law on `[2n]`, lifted by
fibres of size 2 to `[4n]` (with `m = 2`, `q = 3` and a unit window). Its
moment grows from 7.40 at `n = 4` to `2.27e14` at `n = 64`. Over the same
range the uniform law on all matchings of `[4n]` stays below 1.8.

## Survivors (not covered)

* **(P1) Non-projective transfers.** Output kernels that pair labels from
  different input kernel classes on a constant fraction of pairs, as in
  list-decoding soundness and BKM Appendix B style merges. If a fraction
  `delta` of pairs is cross-class, the same count heuristically needs
  `delta >= (1 - 2/q) g / (2n')`. That robust version is not proved here,
  because `theta_*` control fails.
* **(P2) Exponentially many projections.** `k >= exp(Omega(n'/log n'))`, as in
  long-code-type re-encodings (survivor G1 of
  `left-preserving-local-richness-wrappers-are-affine-ug-merges`).
* **(P3) Huge super-blocks.** `R >> kappa^2`, where (T) holds but the bound on
  `theta_*` is not proved.
* **(P4) `q = 2`.** The surplus factor is 1.

This neither proves nor refutes UGC or `finite-moment-pairing-2to1-hardness`.
The exact form of the BKM balanced set is assumed to contain `W_kappa`.
Otherwise (T) and (T1) still hold with `theta_*` as defined.

DERIVATION projective-lift-moment-transfer-proof
