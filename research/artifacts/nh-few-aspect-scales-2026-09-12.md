# Log transport: a representative-free bound on the aspect-ratio discrepancy (2026-09-12)

Lane `nh-few-aspect-scales`. Target: the few-scales route to (CCR) behind
`kt-centralizer-normalization-hs`, from `ccr-under-vertex-rounding-from-few-aspect-scales`.

## Summary

1. **`N_n delta_n -> 0` is not a property of the model.** `delta_n` uses the coordinate
   `sigma_n(t)`.
   - Replacing `sigma_n(t)` by `u_n sigma_n(t)` with `||u_n - 1||_2 -> 0` leaves the ultralimit,
     the rounding `pi_n`, the excess `eps_n` and `N_n` unchanged.
   - It makes `N_n delta_n -> infinity` whenever `N_n -> infinity` and some `F_a(zeta_B)` is
     macroscopically spread.
   - So "`N_n delta_n -> 0` for every rounded model" cannot be proved. Any proof has to pick
     representatives, or use a quantity that ignores them.
2. **A representative-free bound (established, `ccr-under-vertex-rounding-from-log-transport`).**
   Let `pi` be a finite-dimensional unitary representation of `Gamma`, `Lambda <= Gamma`, and
   `theta : Lambda -> Gamma` an isomorphism. Then

   ```text
   D(pi) = tau(log zeta_B) - tau(log zeta_A)  <=  eta*(pi) (2 + log R^m + log R^e) ,
   ```

   - `eta*(pi)` is the total-variation distance between the trace-weighted `Lambda`-type
     distributions of `pi|Lambda` and `pi o theta`;
   - `R^m` and `R^e` are the multiplicity and dimension ranges over the types where the two
     disagree.
3. **Under (H1), with `theta(lambda) = t^(-1) lambda t`.**
   - `eta*(pi_n) <= 2 eps'_n / kappa -> 0`, and `eps_n <= 7 (eta*_n (2 + log(R^m_n R^e_n)))^(1/3)`.
   - (CCR) holds whenever `eta*_n log n' -> 0`, for instance `eps'_n log n' -> 0`. The few-scales
     criterion needed `eps'_n (log n')^3 -> 0`.
   - A counterexample needs mismatched types spanning a multiplicity-times-dimension ratio of
     `exp(Omega(1/eta*_n))`, i.e. order `1/eta*_n` e-folds. Before, the requirement was order
     `1/delta_n ~ (eps'_n)^(-1/3)` dyadic windows.
4. **Not settled.** Nothing here bounds `eta*_n log R_n` for the Theorem E actors, and no cascade
   model was built.

## 1. The operator-level defect depends on the representative

Let `h = F_a(zeta_B)` have spectral projections `P = 1{h >= mu + s}` and `Q = 1{h <= mu - s}`, each
of trace at least `w`.
- **The perturbation.** Choose a partial isometry `V` with `V^* V <= Q`, `V V^* <= P` and
  `tau(V^* V) >= w`. Put `X = V + V^*`. Then `V^2 = 0`, `||X|| <= 1` and `X^2 <= 1`.
- **Commutator lower bound.**
  - `P [X, h] Q = V QhQ - PhP V`.
  - With `x = PhP V - V QhQ`: `tau(V^* x) >= (mu + s) tau(V^* V) - (mu - s) tau(V^* V)`, while
    `|tau(V^* x)| <= ||V||_2 ||x||_2`.
  - So `||[X, h]||_2 >= 2 s ||V||_2 >= 2 s w^(1/2)`.
- **Effect on `delta_n`.** Put `u = exp(i eps X)`. Then `||u - 1 - i eps X|| <= eps^2/2`, so
  `||u h u^* - h||_2 >= 2 eps s w^(1/2) - eps^2`. Replacing `sigma_n(t)` by `u_n sigma_n(t)` gives
  `delta'_n >= 2 eps_n s w^(1/2) - eps_n^2 - delta_n`.
- **Choosing the scale.** With `eps_n = N_n^(-1/2)`: `N_n delta'_n >= 2 s w^(1/2) N_n^(1/2) - 1 - N_n delta_n`.
  - Either `N_n delta_n` already diverges along `U`, or `N_n delta'_n` does.
  - `||u_n - 1||_2 -> 0`, and `t` is not in `Gamma`, so the ultralimit, (H1), `pi_n`, `A_n`,
    `B_n`, `eps_n` and `N_n` are all unchanged.

Genuine `G`-models have `delta_n = 0` and satisfy (CCR). If one of them has `N_n -> infinity`
and a spread profile, then the perturbation gives a model where the few-scales criterion
fails while (CCR) holds.

## 2. The log-transport inequality

- **Types of `pi o theta`.** Write `pi = sum_i m_i rho_i`. Since `theta` is an isomorphism, the
  `rho_i o theta` are pairwise inequivalent irreducible representations of `Lambda`, of dimension
  `d_i`, occurring with multiplicity `m_i` in `pi o theta`. So
  `tau(log zeta_A) = sum_i (m_i d_i/n') log(m_i/d_i) = sum_j w~_j log(m~_j/e_j)`, while
  `tau(log zeta_B) = sum_j w'_j log(m'_j/e_j)`.
- **Entropy form.** Put `f_s(x) = x log(x/s)`. Since `sum_j (e_j/n') m'_j = 1 = sum_j (e_j/n') m~_j`, for
  every `s, s' > 0`:

  ```text
  D = sum_(j in T) (e_j/n') [ f_s(m'_j) - f_s(m~_j) ]  -  sum_(j in T) (e_j/n') (m'_j - m~_j) log(e_j/s') .
  ```

- **Bounds.**
  - Take `s` and `s'` to be the geometric means of the extreme positive multiplicities and
    dimensions over `T`.
  - `|f_s(a) - f_s(b)| <= |a - b| (1 + (1/2) log R^m)`, by the mean value theorem, or directly if
    one of `a, b` is `0`.
  - `|log(e_j/s')| <= (1/2) log R^e`.
  - `sum_j (e_j/n') |m'_j - m~_j| = 2 eta*`.
  - Combining: `D <= eta* (2 + log R^m + log R^e)`.

## 3. From the discrepancy to the excess

- **Jump mass.** `log zeta_B - log zeta_A` is `>= 0` everywhere and `>= log(1+c)` on
  `J = 1{zeta_B >= (1+c) zeta_A}`. So `tau(J) <= D / log(1+c)`.
- **Excess.** The excess lemma gives `eps <= 4 tau(J)^(1/2) + 2c`. With `Y = eta*(2 + log R) < 1`
  and `c = Y^(1/3)`, using `log(1+c) >= c log 2`, this gives `eps <= 7 Y^(1/3)`.
- **Mismatch under rounding.** Item 3 of `vertex-rounding-reduces-ccr-to-commutant-excess`
  supplies `v_n` intertwining `pi_n|Lambda` with `pi~_n`, which is unitarily equivalent to
  `pi_n o theta`.
  - `v_n^* v_n` carries a common subrepresentation with multiplicities `r_j <= min(m'_j, m~_j)`.
  - So `eta*_n = 1 - sum_j min(w'_j, w~_j) <= tau(1 - v_n^* v_n) <= 4 ||1 - v_n||_2^2`.
  - The rate form gives `<= 2 eps'_n / kappa`.

## 4. Consistency with the cascade

Take a telescoping cascade over `L` levels in which restriction merges siblings.
- The type distributions of `pi|Lambda` and `pi o theta` differ only at the two ends, so
  `eta* ~ 1/L`.
- The mismatched types span `L` levels, so `log R ~ L`.
- Hence `eta* log R` is of order one, exactly the regime the bound leaves open.

The inequality is therefore sharp in how it trades mismatch mass against scale range.

## 5. What a proof for the Theorem E actors must supply

- **The quantity to control.** `eta*(pi_n) log R_n -> 0`: the mass where `pi_n|Lambda` and
  `pi_n o theta` disagree must be small against the log range of the disagreeing types.
  Equivalently, rule out mismatch mass `~ 1/L` spread over `L` e-folds.
- **What is now irrelevant.** Neither the compressor coordinate nor a coarse actor gap enters.
  The statement is about one genuine representation of `Gamma`, its restriction to `Lambda`, and
  its transport by `theta`.
- **Where unit-type rounding fits.** `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`
  controls the excess by non-unit mass. The present bound is independent of that congruence
  structure, and the two can be combined on each congruence factor.
