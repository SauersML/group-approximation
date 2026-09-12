---
rg: 2
id: ccr-under-vertex-rounding-from-log-transport
kind: claim
title: The log aspect-ratio discrepancy of a vertex rounding is at most its type mismatch times the log range of mismatched types
distinct_from:
  ccr-under-vertex-rounding-from-few-aspect-scales: that bounds the excess by the operator-level transport defect times the number of occupied dyadic windows, a quantity that depends on the coordinate chosen for the compressor; this bounds the log-trace discrepancy by the total-variation type mismatch of the rounding alone, with the log range of mismatched types in place of the window count, and weakens the rate hypothesis from eps'_n (log n')^3 -> 0 to eps'_n log n' -> 0.
  vertex-rounding-reduces-ccr-to-commutant-excess: that identifies (CCR) with a finite commutant excess and supplies the transport intertwiner; this converts that intertwiner into a bound on the log aspect-ratio discrepancy of the rounding.
  commutant-excess-bounded-by-aspect-ratio-jump-mass: that bounds the excess by the jump mass of zeta_B/zeta_A; this bounds that jump mass through the log-trace discrepancy, using only the type data of one genuine representation.
  unit-type-vertex-rounding-forces-compressor-commutant-rigidity: that makes compressed and ambient images coincide on unit-type congruence factors and bounds the excess by non-unit mass; this bounds the excess for an arbitrary genuine rounding by the type mismatch between the restriction and the transported representation, with no congruence structure.
artifacts:
  - research/artifacts/nh-few-aspect-scales-2026-09-12.md
---

**ESTABLISHED.**

**1. Finite-dimensional inequality.**

Setup:
- `pi` is a unitary representation of a group `Gamma` on `C^(n')`, with normalized trace `tau`.
- `Lambda <= Gamma` is a subgroup and `theta : Lambda -> Gamma` is a group isomorphism.
- As in `commutant-excess-bounded-by-aspect-ratio-jump-mass`: `A = pi(Gamma)'`, `B = pi(Lambda)'`,
  and `zeta_A <= zeta_B` are the aspect-ratio observables.
- `psi_j` runs over the irreducible representations of `Lambda`; `e_j` is the dimension of `psi_j`.

```text
pi|Lambda  = sum_j m'_j psi_j ,          pi o theta = sum_j m~_j psi_j ,
w'_j = m'_j e_j / n' ,                   w~_j = m~_j e_j / n' ,
eta*(pi) = (1/2) sum_j | w'_j - w~_j | ,
D(pi)    = tau(log zeta_B) - tau(log zeta_A)   >=  0 .
```

Put `T = { j : m'_j != m~_j }`. Let `R^m` be the ratio of the largest to the smallest positive
multiplicity among the `m'_j, m~_j` with `j in T`, and `R^e` the ratio of the largest to the
smallest `e_j` with `j in T` (both `1` if `T` is empty). Then

```text
D(pi)  <=  eta*(pi) ( 2 + log R^m + log R^e )  <=  eta*(pi) ( 2 + 2 log n' ) .
```

**2. Under vertex rounding.**

Setting: that of `vertex-rounding-reduces-ccr-to-commutant-excess`:
- a strict compressor `t`, with `Lambda = t Gamma t^(-1)` and `theta(lambda) = t^(-1) lambda t`;
- (H1), with genuine `pi_n` and excess `eps_n`.

Write `eta*_n = eta*(pi_n)` and `R_n = R^m_n R^e_n`. Then:
- **Mismatch vanishes.** `eta*_n <= tau(1 - v_n^* v_n) -> 0` along `U`, with `v_n` the intertwiners of
  item 3 there. With the rate form of `ccr-under-vertex-rounding-from-few-aspect-scales`,
  `eta*_n <= 2 eps'_n / kappa`.
- **Jump mass.** `tau( zeta_B >= (1+c) zeta_A ) <= eta*_n (2 + log R_n) / log(1+c)` for every `c > 0`.
- **Excess.** `eps_n <= 7 ( eta*_n (2 + log R_n) )^(1/3)` whenever `eta*_n (2 + log R_n) < 1`.

**Consequences.**
- **(CCR) from type mismatch.** (CCR) holds whenever `eta*_n log R_n -> 0` along `U`, in particular
  whenever `eta*_n log n' -> 0`, and so whenever `eps'_n log n' -> 0`. The few-scales rate criterion
  needed `eps'_n (log n')^3 -> 0`.
- **Counterexample profile.** Suppose (H1) holds and `lim_U eps_n = delta > 0`.
  - Then `lim_U eta*_n (2 + log R_n) >= (delta/7)^3`, so `log R_n >= ((delta/7)^3 - o(1)) / eta*_n - 2 -> infinity`.
  - So the types where `pi_n|Lambda` and `pi_n o theta` disagree span multiplicity-times-dimension
    ratios of `exp(Omega(1/eta*_n))`: of order `1/eta*_n` e-folds.
- **Representative independence.** `D`, `eta*` and `R` depend only on the rounding `pi_n` and on
  `theta`, not on the coordinate chosen for `sigma(t)`. The operator-level defect `delta_n` of the
  few-scales claim does depend on it.
  - **Hypothesis:** `lim_U N_n = infinity`, and some `F_(a_n)(zeta_B)` has spectral projections of
    trace at least `w > 0` on which it is at least `mu_n + s` and at most `mu_n - s`, for fixed
    `s, w > 0`.
  - **Perturbation:** replacing `sigma_n(t)` by `u_n sigma_n(t)`, with unitaries `||u_n - 1||_2 -> 0`,
    changes neither the ultralimit, nor (H1) with the same `pi_n`, nor `eps_n`, nor `N_n`.
  - **Conclusion:** a suitable choice of `u_n` makes `lim_U N_n delta_n = infinity`. So
    `N_n delta_n -> 0` is not a property of the model, and it cannot be proved for every
    representative.

(CCR) itself stays open. Nothing here bounds `eta*_n log R_n` for the Theorem E actors, and no
root is affected.

Derivation: `ccr-log-transport-proof`.
