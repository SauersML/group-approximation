---
rg: 2
id: fpbs-l2-at-pu-kills-intrinsic-rate-and-stretch
kind: claim
title: Wherever p_(2->2) = p_u < 1 the intrinsic-radius l2 rate vanishes at p_u and linear chemical stretch blows up like 1/(t - p_u), so (IL2) and (UCS) are false on every regular tree times Z^d
distinct_from:
  fpbs-intrinsic-l2-rate-bounded-below-above-pu: that conjectures Lambda(p_u) > 0 on every nonamenable Cayley graph with p_u < 1; this proves Lambda(p_u) = 0 whenever p_(2->2) = p_u, and exhibits such graphs, refuting it
  fpbs-uniform-chemical-stretch-above-pu: that conjectures one linear stretch constant for all t > p_u; this proves K_*(t) >= log(gr)/(2 log(t/p_u)) on the same graphs, refuting it together with its averaged ball form
  fpbs-intrinsic-rates-log-lipschitz-in-parameter: that proves Lambda(t) <= max(0, log(t/p_(2->2))) and the stretch bound at p_c; this evaluates those bounds at p_u on graphs where p_(2->2) reaches p_u, and turns them into refutations of the open side of the intrinsic route
  fpbs-planar-critical-two-sided-dual-piece-mass-infinite: that predicts (UCS) fails on planar {4g,4g} tilings with logarithmic divergence, by critical dual estimates that are still open; this refutes (UCS) outright on tree products, with divergence of order 1/(t - p_u), and uses no critical estimate
  fpbs-planar-stretch-bounded-below-by-dual-piece-mass: that bounds sup_(t>p_u) K_*(t) below by a planar dual mean; this bounds K_*(t) below at each t > p_u by a threshold ratio, on non-planar graphs
---

**ESTABLISHED.** Proof in
`fpbs-l2-at-pu-kills-intrinsic-rate-and-stretch-proof`.

**Notation.** As in `fpbs-intrinsic-l2-rate-closed-zero-set`.

- `G = Cay(Gamma,S)` with `Gamma` finitely generated and nonamenable, and
  `gr > 1` its growth rate.
- `T^(R)_t(u,v) = P_t(d_omega(u,v) <= R)`, with `Lambda(t)` its exponential
  `l2` rate.
- A **linear stretch constant at `t`** is a `K` with
  `inf_(u,v) P_t(d_omega(u,v) <= K(d(u,v)+1)) > 0`. `K_*(t)` is the infimum of
  such `K`.
- An **averaged stretch constant at `t`** is a `K` for which some `c > 0` has

  ```text
  sum_(u,v in B_m) P_t(d_omega(u,v) <= K(2m+1)) >= c |B_m|^2   for all m >= 1.
  ```

  Every linear stretch constant is an averaged one. This is the averaged form
  named in `fpbs-intrinsic-l2-rate-via-uniform-stretch`.

**Theorem.**

1. **(General implication.)** On every such `G`, if `Lambda(p_u) > 0` then

   ```text
   p_u  >=  p_(2->2) e^(Lambda(p_u))  >  p_(2->2).
   ```

   So (IL2), that is `Lambda(p_u) > 0` when `p_u < 1`, implies
   `p_(2->2)(G) < p_u(G)`.
2. **(Vanishing.)** If `p_(2->2)(G) = p_u(G)`, then `Lambda(t) <= log(t/p_u)`
   for every `t >= p_u`. In particular `Lambda(p_u) = 0`.
3. **(Stretch blow-up.)** If `p_(2->2)(G) = p_u(G) < 1` and `K` is an averaged
   stretch constant at some `t in (p_u, 1]`, then

   ```text
   K  >=  log(gr) / (2 log(t/p_u))  >=  p_u log(gr) / (2 (t - p_u)).
   ```

   Hence `K_*(t) -> infinity` as `t ↓ p_u`, at rate at least `1/(t - p_u)`.
   No single `K`, even an averaged one, works on any interval `(p_u, p_u+eps)`.
4. **(Counterexamples.)** Let `T` be the `k`-regular tree with `k >= 3`, and
   let `d >= 1`. The graph `T x Z^d` is a Cayley graph of the nonamenable
   group `(Z/2)^{*k} x Z^d`. For `k = 4` it is also the standard Cayley graph of
   `F_2 x Z^d`. By `fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu`
   it has `0 < p_c < p_u = p_(2->2) < 1`. So on it:
   - `fpbs-intrinsic-l2-rate-bounded-below-above-pu` (IL2) is **false**;
   - `fpbs-uniform-chemical-stretch-above-pu` (UCS) is **false**;
   - the averaged hypothesis of `fpbs-intrinsic-l2-rate-via-uniform-stretch`
     is **false**.

   The same conclusions hold on `T x H` for any infinite amenable Cayley graph
   `H`, and on the lamplighter `LL(T)`, whenever `p_u < 1` there.

**What it kills: an obstruction for a whole class of arguments.**

- **Invariant:** `Lambda(p_u) <= log(p_u / p_(2->2))`. This is item 3 of
  `fpbs-intrinsic-rates-log-lipschitz-in-parameter`, evaluated at `p_u`.
- **Class:** every argument for the flagship statement that passes through a
  positive exponential lower bound, at or just above `p_u`, on
  `<f, K_R g>` or `||K_R||_(2->2)`, where `0 <= K_R <= T^(R)_t` entrywise.
  This includes:
  - uniform or averaged chemical stretch;
  - ball, sphere or other test functions;
  - the whole (UCS) ⇒ (IL2) half of `fpbs-universal-intrinsic-l2-rate-route`.
- **Where every member dies:** at the conclusion `Lambda(p_u) > 0`, or
  `Lambda >= delta` on `(p_u, p_u+eps)`. Such a conclusion forces
  `p_(2->2) < p_u` (item 1), and Hutchcroft--Pan refute that on
  `T x Z^d`, where `p_c < p_u` is true. So these arguments are not merely
  unproved: their intermediate statement is false on graphs that do have a
  window.
- **Survivor:** only (IL1), `lambda_1(p_u) > 0`, is left in
  `fpbs-universal-intrinsic-l2-rate-route`.
  - It is a row-sum (`l1`) statement, `E_(p_u)|B^int_R(o)| >= e^(delta R)`.
  - Item 1 does not apply to it, because `lambda_1 >= Lambda` can be strict.
  - A proof of (IL1) must bound expected intrinsic ball volume directly, and
    must not go through any `l2` pairing of truncated kernels.

**Cross-node incompatibility.** Take any Cayley graph with `p_u < 1` and an
infinite amenable normal subgroup `N`. By C2 of
`fpbs-relative-threshold-is-quotient-l2-threshold`, Claim E at `(G,N)` is
equivalent to `p_(2->2) = p_u`. By item 1, (IL2) at `G` implies
`p_(2->2) < p_u`. So at most one of (IL2) and Claim E holds at each such
`(G,N)`.

Question Q of `research/artifacts/fpbs-amenable-normal-fibre-mass-bound-2026-09-16.md`
asks whether `p_(2->2) = p_u` on this whole class, for example on `F_2 x Z`
with every generating set. A positive answer would refute (IL2) on the entire
class.

**Remark (IL1 sanity, elementary).** For every `t`,
`E_t|B^int_R(o)| >= |S_R| t^R` (test one geodesic to each sphere point).
So `lambda_1(t) >= max(0, log(t gr))`, and (IL1) holds on any graph with
`p_u gr > 1`. On `T x Z^d`, `gr = k - 1`, so (IL1) holds there if
`p_u(T x Z^d) > 1/(k-1) = p_c(T)`.

That inequality is recalled for large `k`, as Grimmett--Newman type bounds
with nonuniqueness up to order `k^(-1/2)`. It is not imported here. If it
holds, these graphs separate (IL1) from (IL2): (IL1) is true and (IL2) is
false.
