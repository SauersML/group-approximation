---
rg: 2
id: vertex-rounding-reduces-ccr-to-commutant-excess
kind: claim
title: Under stable vertex rounding, compressor commutant rigidity is the vanishing of a finite commutant excess, and aspect-ratio transport is automatic
distinct_from:
  ccr-holds-for-all-genuine-fd-coordinate-models: that proves (CCR) when the whole actor is coordinatewise a genuine finite-dimensional representation; this assumes genuine rounding only on the Kazhdan vertex and reduces (CCR) to a finite-stage excess of the rounded vertex commutants, without proving it.
  commutant-no-growth: that is exact no-growth for genuine representations of the ambient group; this is the asymptotic setting where the restriction to the compressed copy is only flexibly equivalent to the transported representation.
  hs-normalization-needs-coarse-actor-scale-pinning: that is the conditional median assembly; this proves that its transport hypothesis (H3), in the multiplicative all-scales form the median step consumes, follows from its rounding hypothesis (H1), and identifies (CCR) with a finite-dimensional quantity.
artifacts:
  - research/artifacts/hs-scale-pinning-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma < G`, let `t` be a strict compressor, and put
`Lambda = t Gamma t^(-1) <= Gamma`. Let `(F, kappa)` be a Kazhdan pair for `Gamma`.
Let `sigma_n : G -> U(n)` be a trace-preserving asymptotic representation, with
`M = prod_U M_n`.

Assume (H1) of `hs-normalization-needs-coarse-actor-scale-pinning`. After `o(n)`
padding there are genuine `pi_n : Gamma -> U(n')`, with `n'/n -> 1` and
`max_(s in F) ||sigma_n(s) - pi_n(s)||_2 -> 0`. Put

```text
A_n = pi_n(Gamma)',   B_n = pi_n(Lambda)',
eps_n = sup { ||x - E_(A_n) x||_2 : x in B_n, ||x|| <= 1 },
```

where `E_(A_n)` is the trace-preserving conditional expectation onto `A_n`. Then:

1. `sigma(Gamma)' cap M = prod_U A_n` and `sigma(Lambda)' cap M = prod_U B_n`.
2. (CCR), `sigma(Lambda)' cap M <= sigma(Gamma)' cap M`, holds iff `lim_U eps_n = 0`.
3. There are partial isometries `v_n` with `v_n pi_n(lambda) = pi~_n(lambda) v_n` for all `lambda` in
   `Lambda`, and `||v_n - 1||_2 -> 0`. Here `pi~_n(lambda) = sigma_n(t) pi_n(t^(-1) lambda t) sigma_n(t)^*`.
4. Let `zeta_A` and `zeta_B` be the aspect-ratio observables `sum (multiplicity / irreducible
   dimension)` over the minimal central projections of `A_n` and `B_n`, and let
   `F_a(x) = x/(x+a)`. Then

   ```text
   sup_(a > 0) || F_a(zeta_B) - sigma_n(t) F_a(zeta_A) sigma_n(t)^* ||_2  ->  0   along U.
   ```

**Reading.**
- Item 4 is hypothesis (H3) of the conditional assembly, in the multiplicative, all-scales
  form the median step consumes. It needs nothing beyond (H1), so (H3) is redundant.
- The additive `L^1` form of (H3) is too weak. Take an irreducible `pi` of dimension `n` that
  splits into two inequivalent halves on `Lambda`. Then `||zeta_B - zeta_A||_1 = 1/n`, while
  `eps = 1/2`.
- With `commutant-excess-bounded-by-aspect-ratio-jump-mass`, item 2 turns (CCR) into
  `tau(zeta_B >= (1+c) zeta_A) -> 0` for every `c > 0`.

(CCR) itself stays open, and no root is affected.

Derivation: `vertex-rounding-ccr-reduction-proof`.
