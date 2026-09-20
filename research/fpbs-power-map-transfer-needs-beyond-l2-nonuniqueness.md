---
rg: 2
id: fpbs-power-map-transfer-needs-beyond-l2-nonuniqueness
kind: claim
title: Power-map transfer of the gap between generating sets needs a source with p_u squared above p_c, which fails on every tree-times-amenable graph and cannot be certified spectrally
distinct_from:
  fpbs-generating-set-threshold-comparison: that proves the power-map inequalities and the nested transfer rules; this proves every certificate built from them needs p_u(T)^2 > p_c(T) at the source, and that the known gapped product graphs and all spectral certificates fail this.
  fpbs-lossless-move-comparison-fails-marginal-transfer: that shows the lossless two-path comparison keeps an exponent-2 Remove window and names the residual band; this shows every power-map certificate, chained or relative, is void on sources with p_2 = p_u, and that the Hutchcroft--Pan product graphs all sit in that band.
  fpbs-l2-at-pu-kills-intrinsic-rate-and-stretch: that uses p_(2->2) = p_u against intrinsic rate and stretch arguments on one graph; this uses p_2 <= sqrt(p_c) against transfer between two Cayley graphs of one group.
---

**ESTABLISHED (calibration, class obstruction).** Proof:
`fpbs-power-map-transfer-needs-beyond-l2-nonuniqueness-proof`.

**Setting.** `Gamma` is a finitely generated group. `T = Cay(Gamma,S_T)` and
`G = Cay(Gamma,S_G)` with `S_T ≠ S_G`, both finite, symmetric and without `e`.
The maps `phi` (for `S_G`-words over `S_T`) and `psi` (for `S_T`-words over
`S_G`) come from `fpbs-generating-set-threshold-comparison`. Take `phi = id`
when `S_G ⊆ S_T`, and `psi = id` when `S_T ⊆ S_G`; these are the nested
monotone bounds. Define the **source margin**

```text
mu(T) = p_u(T)^2 - p_c(T).
```

A **pure power-map certificate** of `p_c(G) < p_u(G)` from `T` is a chain
`T = T_0, ..., T_m = G` of Cayley graphs of `Gamma`. It uses only these
bounds at each step:

- `p_u(T_(i+1)) >= phi_i(p_u(T_i))`;
- `p_c(T_(i+1)) <= psi_i^(-1)(p_c(T_i))`.

The **relative variant** replaces `p_u` by `p_c(I;.)` for an amenable
wq-normal subgroup `I`. There `p_c(I;.) = p_u(.)`, by
`fpbs-amenable-wq-normal-pu-is-relative-pc`.

**Claim.**

1. **Margin law.** Every pure certificate, chained or relative, gives
   `p_c(T) < p_u(T)^N`, where `N = prod(L_i L'_i) >= 2`. So it needs
   `mu(T) > 0`, that is,

   ```text
   p_u(T)  >  sqrt(p_c(T))  >=  p_2(T)  >=  p_(2->2)(T).
   ```

   In words, the source must be nonunique at parameters where
   `tau_p(o,.)` is not in `l^2`.
2. **Void on the Hutchcroft--Pan class.** Suppose `p_u(T) <= p_2(T)`, for
   instance because `p_(2->2)(T) = p_u(T)`. Then
   `mu(T) <= 0`, and no pure certificate starts at `T`. This holds
   unconditionally when `T = T_k □ H`, with `k >= 3` and `H` an infinite
   amenable Cayley graph, because there `p_(2->2) = p_u`. That covers every
   generating set of `F_n x A` of the form (free basis) ⊔ `S_A`, and every
   generating set of `(Z/2)^(*k) x A` of the form (standard involutions)
   ⊔ `S_A`, with `A` infinite amenable. On these graphs `p_u(T) <= sqrt(p_c(T))`.
3. **Spectral sources are impossible.** For every Cayley graph `T` of degree
   `d >= 3`,

   ```text
   (1/sigma(Lambda_T))^2  <=  1/(d-1)  <=  p_c(T),
   ```

   and `1/||A_T|| <= 1/sigma(Lambda_T)`. So neither
   `p_u >= 1/sigma(Lambda)` (Theorem 1 of
   `fpbs-nb-spectral-deficit-obstruction`) nor `p_u >= 1/||A||` ever certifies
   `mu(T) > 0`. A usable source needs a non-spectral lower bound on `p_u`.
   - *Such bounds exist:* on Cayley graphs with infinitely many ends, such as
     trees and nontrivial free products other than `Z/2 * Z/2`, `p_u = 1`
     and `p_c < 1`, so `mu > 0`.
   - *So do planar ones:* on the genus-`g` surface groups with standard
     generators (`g >= 2`), `p_u = 1 - p_c` and `p_c <= 0.1503`. Hence
     `mu >= 0.849^2 - 0.1503 > 0.57`.
4. **Hybrid certificates.** Suppose one threshold of `G` is certified
   intrinsically and the other by a lossy transfer from `T` with
   `mu(T) <= 0`. Then the intrinsic side must beat the source itself:
   - **`p_u` transferred, `S_G ⊄ S_T`:** it needs an intrinsic bound
     `p_c(G) < p_u(T)^2 <= p_c(T)`.
   - **`p_c` transferred, `S_T ⊄ S_G`:** it needs an intrinsic bound
     `p_u(G) > sqrt(p_c(T)) >= p_u(T)`.

**What this kills.** The power-map method on
`fpbs-gap-survives-product-generator-moves`, together with every chain of Add
and Remove moves, can only export a gap. It cannot manufacture one. It exports
only from sources in the region `p_u > sqrt(p_c)`.

- The canonical gapped graphs of the amenable-normal class are the
  Hutchcroft--Pan products `T_k □ H` (with product generating sets). By
  item 2, every one of them lies outside that region.
- The other known gapped graphs of that class are certified spectrally, for
  example the Pak--Smirnova-Nagnibeda powers. By item 3, no such certificate
  places them inside the region.
- So the "residual band" `p_c(T) <= p_u(T) <~ sqrt(p_c(T)/N)` of
  `fpbs-lossless-move-comparison-fails-marginal-transfer` is not an
  exceptional place where a counterexample must hide. The canonical sources
  live exactly there.
- *Invariant:* `mu(T)`.
- *Step where every member dies:* the final inequality
  `p_c(T) < Psi(p_u(T))`, because `Psi(p) <= p^2` while
  `p_u(T)^2 <= p_2(T)^2 <= p_c(T)`.

**Conditional extension (not established).** Assume Claim E of
`fpbs-relative-threshold-is-quotient-l2-threshold`. Its item C2 gives
`p_(2->2) = p_u` whenever the relevant subgroup is amenable normal. Then item 2
extends to every Cayley graph with an infinite amenable normal subgroup, and
the method is void on the whole amenable-normal class.

**Remark (not a prerequisite).** Hutchcroft's hyperbolic theorem, imported in
`fpbs-hyperbolic-and-nonunimodular-nonuniqueness`, gives `p_c < p_u` on every
nonamenable Gromov-hyperbolic Cayley graph. The `mu > 0` sources certified
here are hyperbolic: trees, virtually free groups, and surface groups. Since a
transfer stays inside one group, they yield no Cayley graph that is not
already covered.

The groups the target cares about are `F_n x A` with a non-product generating
set. Every gapped source known for them is one of two kinds:

- a Hutchcroft--Pan product, which has `mu <= 0` by item 2; or
- a graph certified spectrally, such as the Pak--Smirnova-Nagnibeda powers
  `S^k`. For these, item 3 shows the certificate carries no information about
  `mu`.

## Attempts
