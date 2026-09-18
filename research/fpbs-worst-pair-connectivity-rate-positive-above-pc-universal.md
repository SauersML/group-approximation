---
rg: 2
id: fpbs-worst-pair-connectivity-rate-positive-above-pc-universal
kind: claim
title: On every nonamenable Cayley graph some p above p_c has a point in every large ball connected to the centre with exponentially small probability
distinct_from:
  fpbs-sphere-two-point-rate-below-arccosh-universal: that kernel (G) is a sphere-sum bound below arccosh(1/rho); this is a worst-pair bound, strictly weaker (it holds on the whole interval (p_c,1) of T_d, while (G) holds only below 1/sqrt(d-1))
  fpbs-sphere-two-point-rate-right-continuous-universal: that asks g(p) -> 0 at p_c+; this asks only one exponentially rare pair per radius at one p > p_c
  fpbs-intrinsic-growth-rate-positive-at-pu: that is a positive chemical-radius rate at p_u; this is a positive extrinsic worst-pair decay rate just above p_c
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
---

**OPEN (kernel K).** Let `G` be a Cayley graph of a finitely generated
nonamenable group. Then some `p > p_c` and some `c > 0` satisfy, for infinitely
many `n`,

```text
min_(v in B_n) tau_p(o,v)  <=  e^(-cn).
```

Since `-(1/n) log kappa_p(n)` converges (item 1 of
`fpbs-worst-pair-connectivity-rate-kernel`), this is exactly `gamma(p) > 0`.

**What it gives.** `p_c < p_u`, by item 4 of
`fpbs-worst-pair-connectivity-rate-kernel`. The kernels (EG), (G) and (K')
each imply (K).

**Position.**

- **Converse.** `p_c < p_u` gives `kappa_p(n) -> 0` for `p in (p_c,p_u)`, via
  Lyons–Schramm indistinguishability (recalled, not imported), but not an
  exponential rate. So (K) is at most one "exponential versus subexponential
  decay in the nonuniqueness phase" step from the flagship statement.
- **Where a collapse must live: a jump of size at least log gr.** Hutchcroft
  arXiv:1605.05301v1, Theorem 2, as transcribed in Section (c) of the artifact:
  `kappa_(p_c)(n) <= gr^(-n)`. That gives `gamma(p_c) >= log gr`, recalled
  here and not load-bearing. So (K) fails exactly when the left-continuous
  function `gamma` drops from at least `log gr` at `p_c` to `0` on
  `(p_c,1]`. On `T_d`, `gamma(p) = -log p` is continuous.
- **The class that cannot prove it.** By item 6, no finite-radius
  certificate at `p_c` or above bounds `gamma` from below. Unlike Simon–Lieb
  (submultiplicative, where one radius suffices), `kappa` is
  *super*multiplicative. So a proof must control every radius at once, in
  the same way that `kappa_p(n) |B_n| <= chi_p` does for `p < p_c`.
- **The supercritical substitute that is missing.** Split
  `tau_p(o,v) = P_p(o <-> v, |K_o| < infinity) + P_p(o <-> v, |K_o| = infinity)`.
  Summing over `B_n`, (K) follows from these two statements at one `p > p_c`:
  - (a) `E_p[|K_o ∩ B_n| ; |K_o| = infinity] <= e^((log gr - c)n)`: infinite
    clusters have expected extrinsic growth strictly below `gr`;
  - (b) `E_p[|K_o| ; |K_o| < infinity] = e^(o(n))`, where the left side is the
    finite-cluster susceptibility, or merely its ball truncation.

  Each of (a) and (b) can fail, and neither is in the graph.

## Attempts

1. **Conditional chemical slope at the critical worst pairs
   (2026-09-18, swarm-0917-w7-w7-bs-follow).**
   - **Established:** `fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff`.
     - It proves `kappa_(p_c)(n) <= gr^(-n)` from subcritical sharpness
       alone, by Fekete and lower semicontinuity. So `gamma(p_c) >= log gr`
       is now load-bearing, not merely recalled.
     - It proves `gamma(t) + l(t) log(t/p_c) >= gamma(p_c)` for all
       `t > p_c`. Here `l(t)` is the conditional chemical slope of the
       `p_c`-minimisers.
     - The inequality is an equality on `T_d` at every `t`.
   - **New route:** `fpbs-worst-pair-rate-via-chemical-slope`, through the OPEN
     kernel (CS), `fpbs-worst-pair-chemical-slope-below-threshold-universal`.
   - **Obstruction:** a collapse forces `l(p_c+epsilon) >= p_c log(gr)/epsilon`.
     Every unconditional stretch or short-path construction is capped at the
     same threshold (tradeoff item 5), so it cannot prove (CS).
   - **Correction to the Position section:** input (b) of the (a)/(b) split
     is already in the graph. `fpbs-supercritical-finite-susceptibility`
     (Hermon–Hutchcroft, via `fpbs-hermon-hutchcroft-finite-tail-input`) gives
     `E_p[|K_o|; |K_o| < infinity] < infinity` for every `p > p_c`. So the
     split needs only (a), which is a ball form of (K').
