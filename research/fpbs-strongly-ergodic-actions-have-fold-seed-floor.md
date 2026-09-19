---
rg: 2
id: fpbs-strongly-ergodic-actions-have-fold-seed-floor
kind: claim
title: For every non-atomic p.m.p. action of F(a,b), the 2-of-3 fold seed density satisfies sigma_b >= (1 - rho_X)/4, so strongly ergodic actions have sigma_b > 0 and the Bernoulli class has sigma_b >= (2 - sqrt 3)/8 at every depth
distinct_from:
  fpbs-weakly-bernoulli-fold-seeds-have-density-floor: that proves sigma_b >= 1/80 (best 0.01406) only on the weak-containment class of Bernoulli, by a first-moment count on random permutation models; this is a deterministic isoperimetric-spectral bound valid for every non-atomic action with a spectral gap, and gives (2 - sqrt 3)/8 = 0.0335 on the Bernoulli class.
  fpbs-mal-bernoulli-single-stage-floor: that asks for a floor on relC over all graphings; this bounds only the one-double-coset quantity sigma_b and, through Theorem B, graphings of bounded b-length.
  fpbs-mal-graphing-b-length-weighted-floor: that transfers any sigma_b floor to b-length-weighted graphing mass; this supplies a larger sigma_b floor on a larger class of actions.
artifacts:
  - research/artifacts/fpbs-spectral-fold-seed-floor-2026-09-18.md
  - experiments/fpbs-z3-overgroup-2026-09-17/spectral_check.py
  - experiments/fpbs-z3-overgroup-2026-09-17/spectral_check_out.txt
---

**ESTABLISHED** through `fpbs-strongly-ergodic-actions-have-fold-seed-floor-proof`.

Let `L = F(a, b)` act p.m.p. on a non-atomic standard space `(X, μ)`; no
freeness is assumed. With `T_w = (w, a w, b w)`, `cl` the 2-of-3 closure (with
multiplicity) and `sigma_b(X) = inf { μ(A) : cl(A) conull }`, put
`M = (1/4)(a + a^{-1} + b + b^{-1})` and
`rho_X = sup { <Mf, f>/||f||^2 : 0 ≠ f ∈ L^2_0 real }`.

**Claim (Theorem S).**

```text
sigma_b(X)  ≥  inf_{μ(I)=1/2} μ( I \ (a^{-1}I ∩ b^{-1}I) )
            ≥  (1/2) inf_{μ(I)=1/2} max_{s∈{a,b}} μ(I Δ sI)
            ≥  (1 − rho_X)/4 .
```

**Consequences.**

1. If `X` is strongly ergodic then `sigma_b(X) > 0`. This is the open
   direction of the conjecture "`sigma_b > 0` iff strongly ergodic" in §4.4
   of the w11 census artifact `fpbs-congruence-fold-census-2026-09-18.md`
   (node `fpbs-mal-profinite-fold-density-is-finite-percolation`, integration
   branch), for all non-atomic actions. For profinite `X` with levels `Q_n` it
   reads `sigma_b(X) ≥ inf_n (1 − λ_2(Q_n))/4`.
2. If `X` is non-atomic and weakly contained in a Bernoulli shift of `L`, then
   for every `j ≥ 0`, with `φ(a) = a`, `φ(b) = b a b^{-2}`,
   `sigma_b(X ∘ φ^j) ≥ (1 − rho)/4 = (2 − √3)/8 ≈ 0.0335`. Here
   `rho = √3/2` is Kesten's spectral radius of `F_2`; positivity needs only
   `rho < 1`.
3. By Theorem B (`fpbs-mal-graphing-b-length-weighted-floor`), on every free
   action every generating graphing of `R_L` over `R_K` has
   `Σ_h |h|_{K,b} μ(D_h) ≥ (1 − rho_X)/4`.
