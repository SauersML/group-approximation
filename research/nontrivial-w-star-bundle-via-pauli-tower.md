---
rg: 2
id: nontrivial-w-star-bundle-via-pauli-tower
kind: route
title: The Pauli tower's completion has the scalar point property, which no trivial R-fibre bundle has
target: nontrivial-w-star-bundle-with-r-fibres-exists
requires: [pauli-tower-bundle-has-scalar-point-property]
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
---

**UNREVIEWED** (lane `ex2-tw-unsplittable-tails`, 2026-09-13). An `ex-verify-analysis` review is
requested before this is described as settling BBSTWW Question 3.14.

1. **The witness.** The prerequisite gives a strictly separable continuous W*-bundle `M` over the
   compact metrizable space `X̂ = Π_k (RP^{4^{k−1}} × RP^{2·4^{k−1}})`, every fibre `R`. It is the
   uniform tracial completion of a unital separable nuclear `C(X̂)`-algebra with `M_{2^∞}` fibres
   and twisted `M_2`-bundle factors with Pauli holonomy.
2. **The invariant.** Every self-adjoint element of `M` is scalar at some point of `X̂`.
3. **Trivial bundles lack it.** In `C_σ(X̂, R)` the constant section `e`, with `e ∈ R` a projection of
   trace `1/2`, has `E(e²) − E(e)² ≡ 1/4`. W*-bundle isomorphisms preserve `E`, hence this variance.
4. So `M ≇ C_σ(X̂, R)`.

**What makes it work.** The existence gap sits at the unit, not in comparison:
- no uniformly large order zero `M_2` (`pauli-tower-bundle-has-no-uniform-order-zero-m2`);
- no soft half splitting of any tail (`pauli-tower-sections-are-somewhere-scalar`).

This is the shape recorded on the target's Attempts ("certified by an existence gap at a constant
profile"). The base contains a Hilbert cube, as `bauer-gamma-failure-localizes-to-infinite-dim-point`
requires.
