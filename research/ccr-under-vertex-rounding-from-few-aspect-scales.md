---
rg: 2
id: ccr-under-vertex-rounding-from-few-aspect-scales
kind: claim
title: Under vertex rounding, the commutant excess is at most the transport defect times the number of occupied aspect-ratio scales
distinct_from:
  vertex-rounding-reduces-ccr-to-commutant-excess: that proves (CCR) is the vanishing of a finite commutant excess and that aspect-ratio transport holds uniformly over all scales; this sums that transport over dyadic scales and bounds the excess by the transport defect times the number of occupied scales, with no actor gap.
  commutant-excess-bounded-by-aspect-ratio-jump-mass: that bounds the excess by the jump mass of the aspect ratio; this bounds the jump mass itself, one dyadic window at a time, by trace conservation along the compressor.
  hs-normalization-needs-coarse-actor-scale-pinning: that is the conditional assembly (H1) + (H2') => (CCR), which spends a coarse actor gap; this proves (CCR) from (H1) alone whenever the aspect-ratio profile occupies few dyadic scales relative to the transport defect, so the actor gap matters only for profiles spread over unboundedly many scales.
  ccr-holds-for-all-genuine-fd-coordinate-models: that proves (CCR) when every coordinate is a genuine representation of the ambient group; this assumes genuine rounding only on the Kazhdan vertex and never uses property (T) of the ambient group.
artifacts:
  - research/artifacts/hs-coarse-gap-aspect-scales-2026-09-12.md
---

**ESTABLISHED.** Use the setting and notation of
`vertex-rounding-reduces-ccr-to-commutant-excess`:
- `Gamma < G`, a strict compressor `t`, `Lambda = t Gamma t^(-1) <= Gamma`, and a Kazhdan
  pair `(F, kappa)` for `Gamma`;
- a trace-preserving asymptotic representation `sigma_n : G -> U(n)` satisfying (H1), with
  genuine `pi_n : Gamma -> U(n')`, regarded after the padding of (H1) on `C^(n')`;
- `A_n = pi_n(Gamma)'`, `B_n = pi_n(Lambda)'`, the commuting aspect-ratio observables
  `zeta_A <= zeta_B`, and the excess `eps_n`.

Put `F_a(x) = x/(x+a)` and

```text
delta_n = sup_(a>0) || F_a(zeta_B) - sigma_n(t) F_a(zeta_A) sigma_n(t)^* ||_2 ,
```

which tends to `0` along `U` by item 4 of that claim. Let `N_n` be the number of
dyadic windows `[2^k, 2^(k+1))`, `k in Z`, meeting the spectrum of `zeta_A`. Then
`N_n <= log_2(zeta_max / zeta_min) + 2 <= 2 log_2 n' + 2`, and for every `0 < c < 1`:

1. **One window.** For every `a > 0`,
   `tau( 1{a <= zeta_A < 2a} 1{zeta_B >= (1+c) zeta_A} ) <= (15/c) delta_n`.
2. **Jump mass.** `tau( zeta_B >= (1+c) zeta_A ) <= 15 N_n delta_n / c`.
3. **Excess.** `eps_n <= 4 (15 N_n delta_n / c)^(1/2) + 2c`. In particular
   `eps_n <= 18 (N_n delta_n)^(1/3)` whenever `N_n delta_n < 1`.

**Consequences.**
- **(CCR) from vertex rounding and few scales.** If `N_n delta_n -> 0` along `U`, then
  (CCR) holds. No property (T) of `G`, no actor gap and no block decomposition is used.
  Property (T) enters only for `Gamma`, through item 4.
- **Tight profiles.** More generally, (CCR) holds if for every `epsilon > 0` there is
  `K(epsilon)` such that, along `U`, all but `epsilon` of the trace of `zeta_A` lies in
  `K(epsilon)` dyadic windows.
- **What a counterexample must look like.** Suppose (H1) holds and (CCR) fails, with
  `lim_U eps_n = delta > 0`. Then the jump mass at `c = delta/4` has limit at least
  `c_0 = (delta/8)^2`. Any family of dyadic windows capturing all but `c_0/2` of the trace
  of `zeta_A` has at least `(c_0 delta / (120 delta_n)) (1 - o(1)) -> infinity` windows, and
  each window carries jump mass at most `15 delta_n / c`. So every counterexample spreads
  its aspect-ratio profile over unboundedly many dyadic scales, at least of order
  `1/delta_n` of them.
- **Log-trace criterion.** Put `D_n = tau(log zeta_B) - tau(log zeta_A) >= 0`. Then
  `tau(zeta_B >= (1+c) zeta_A) <= D_n / log(1+c)`, so `D_n -> 0` implies (CCR). With
  `p_i = m_i d_i / n'`, `tau(log zeta_A) = log n' - H(p) - 2 sum_i p_i log d_i`, where `H` is
  the Shannon entropy.
- **Rate form.** Put `eps'_n = max_(s in F) || pi~_n(t s t^(-1)) - pi_n(t s t^(-1)) ||_2`,
  the transported rounding defect of item 3, with
  `pi~_n(lambda) = sigma_n(t) pi_n(t^(-1) lambda t) sigma_n(t)^*`.
  - The proof of item 4 gives `delta_n <= 10 (eps'_n / kappa)^(1/3)` when `eps'_n <= kappa`.
  - Hence (CCR) holds whenever `(eps'_n)^(1/3) log(zeta_max / zeta_min) -> 0`, for instance
    whenever `eps'_n (log n')^3 -> 0`.
  - Amplification `sigma_n (x) 1_k` leaves `zeta_max / zeta_min` and the defects unchanged,
    so the criterion is intrinsic to the model.

(CCR) itself stays open. Nothing here bounds `N_n delta_n` for an arbitrary hyperlinear
model, and no root is affected.

Derivation: `ccr-few-aspect-scales-proof`.
