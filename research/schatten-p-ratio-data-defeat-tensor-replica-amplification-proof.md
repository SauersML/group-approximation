---
rg: 2
id: schatten-p-ratio-data-defeat-tensor-replica-amplification-proof
kind: route
title: Compute the replicated eigenvalue measures by Fourier coefficients and split replica degrees at the relator saturation scale
target: schatten-p-ratio-data-defeat-tensor-replica-amplification
requires: []
artifacts:
  - experiments/schatten-p-tensor-replica-2026-09-17/check_schatten_replicas.py
  - experiments/schatten-p-tensor-replica-2026-09-17/output.txt
---

The proof is a direct computation with no external input. The notation is that of the claim. Throughout, `m` is
large enough that `eta, rho <= 1/4` and `eps, x <= 1`.

## 0. Facts

- **(F1) Replicas.** Every measure in the claim is invariant under `lambda -> conj(lambda)`. So
  `Phi_(i,j) mu = mu^(*n)` with `n = i + j`.
- **(F2) Fourier.** For such a `mu`, the coefficient `hat mu = int lambda dmu` is real, and
  `L_2(mu^(*n))^2 = 2 - 2 (hat mu)^n`.
- **(F3) Comparison.** Use Jensen, and `|lambda - 1| <= 2`.
  - For `p >= 2`: `L_p >= L_2`.
  - For `p <= 2`: `L_p <= L_2` and `L_p^p >= 2^(p-2) L_2^2`.
- **(F4) Mixtures.** By (R), `L_p^p`, `L_2^2` and `L_rk` of `Phi mu` are `w`-averages over the summands, and `L_op`
  is a maximum.
  - A ratio of two `w`-averages is at least the least summand ratio.
  - So (iii) reduces to single summands `mu^(*n)`, `n >= 1`.
- **(F5) Elementary bounds.**
  - `cos t <= e^(-t^2/2)` for `|t| <= pi/2`.
  - `1 - s^n <= n(1 - s)` on `[0,1]`.
  - `1 - e^(-s) >= (1 - e^(-1)) min(1, s)`.
- **(F6) Relator atoms.** Let `nu = (1 - rho) e(theta) + rho delta_(-1)`, with `0 < rho <= 1/4`, `theta <= 1` and
  `theta/pi` irrational.
  - `nu^(*n)` is the law of `exp(i(theta J + pi F))`. Here `F ~ Bin(n, rho)`, and `J` is a sum of `n - F` independent
    signs.
  - The value is `1` only if `J = 0` and `F` is even. So `nu^(*n)({1}) <= rho^n + 1/2`, because a simple walk of length
    `k >= 1` sits at `0` with probability at most `1/2`. Hence `L_rk(nu^(*n)) >= 1/4`.
  - The event `F = 1`, `J in {0, +-1}` has positive mass. It puts an atom at `-e^(i theta j)` with `|j| <= 1`, so
    `L_op(nu^(*n)) >= 2 cos(1/2) > 1.75`.
  - The witnessed element always has `L_op <= 2` and `L_rk <= 1`. So the op and rank ratios of (iii) are at least
    `0.87` and `1/4` on every summand, in both cases below.

## 1. Case `p > 2`, data (S>)

**Spectra.**
- `mu^(*n) = (1 - q_n) delta_1 + q_n delta_(-1)`, with `q_n = (1 - (1 - 2 eta)^n)/2 <= min(n eta, 1/2)`.
- So `L_p(mu^(*n))^p = 2^p q_n` and `L_2(mu^(*n))^2 = 4 q_n`.
- `hat nu = (1 - rho) cos eps - rho` lies in `[-rho, cos eps]`, and `rho < cos 1 <= cos eps`.
- Hence `(hat nu)^n <= cos^n eps` for every `n`. By (F2), (F5) and (F3),

```text
L_p(nu^(*n))^2 >= L_2(nu^(*n))^2 >= 2 - 2 exp(-n eps^2 / 2).                                        (1)
```

**(i).**

```text
L_p(nu)^p / L_p(mu)^p <= (eps^p + 2^p rho) / (2^p eta) -> 0.
```

**(ii).**
- Put `N* = ceil(2/eps^2)`.
  - If `n >= N*`, (1) gives `L_p(nu^(*n))^p >= (2 - 2/e)^(p/2) >= 1`.
  - If `n < N*`, then `L_p(mu^(*n))^p <= 2^p N* eta <= 2^p delta_m`, where `delta_m = (2/eps^2 + 1) eta -> 0`.
- For a replica with weights `w_k` and degrees `n_k`, let `W` be the weight of the summands with `n_k >= N*`.
- Since `q <= 1/2`, we get `L_p(Phi mu)^p <= 2^(p-1) W + 2^p delta_m`.
- So `L_p(Phi mu) >= c` forces `W >= 2^(1-p) c^p - 2 delta_m`. Then

  ```text
  L_p(Phi nu)^p >= W >= 2^(-p) c^p
  ```

  once `2 delta_m <= 2^(-p) c^p`. That is `L_p(Phi nu) >= c/2`.

**(iii), HS.** For one summand, by (1) and (F5),

```text
L_2(nu^(*n))^2 / L_2(mu^(*n))^2  >=  2(1 - 1/e) min(1, n eps^2/2) / (4 min(n eta, 1/2)).
```

- If `n eps^2 >= 2`, this is at least `1 - 1/e`.
- Otherwise it is at least `(1 - 1/e) eps^2/(4 eta)`, which tends to `infinity`.
- So the HS ratio is at least `(1 - 1/e)^(1/2) > 1/4` for large `m`.
- The op and rank ratios are covered by (F6).

## 2. Case `1 <= p < 2`, data (S<)

**Spectra.**
- `hat mu = cos x`. By (F2) and (F5), `L_2(mu^(*n))^2 = 2 - 2 cos^n x <= min(n x^2, 4)`.
- By (F3), `L_p(mu^(*n))^p <= (n x^2)^(p/2)`.
- `hat nu = (1 - rho) cos y - rho` lies in `[0, 1 - 2 rho]`. So by (F3),

```text
L_2(nu^(*n))^2 >= 2 - 2 exp(-2 n rho),      L_p(nu^(*n))^p >= 2^(p-2) (2 - 2 exp(-2 n rho)).       (2)
```

**(i).** Since `|e^(ix) - 1| >= 2x/pi`,

```text
L_p(nu)^p / L_p(mu)^p <= (pi/2)^p (y^p + 2^p rho) / x^p -> 0.
```

**(ii).**
- Put `N* = ceil(1/rho)`.
  - If `n >= N*`, (2) gives `L_p(nu^(*n))^p >= 2^(p-2)(2 - 2e^(-2)) >= 0.43 * 2^p`.
  - If `n < N*`, then `L_p(mu^(*n))^p <= ((1/rho + 1) x^2)^(p/2) =: delta_m -> 0`, because `x^2/rho -> 0`.
- So `L_p(Phi mu)^p <= 2^p W + delta_m`, and `L_p(Phi mu) >= c` forces `W >= 2^(-p)(c^p - delta_m)`. Then

  ```text
  L_p(Phi nu)^p >= 0.43 * 2^p W >= 0.43 (c^p - delta_m) >= 0.4 c^p
  ```

  for large `m`. So `L_p(Phi nu) >= 0.4^(1/p) c >= c/5`.

**(iii), HS.** For one summand, by (2) and (F5),

```text
L_2(nu^(*n))^2 / L_2(mu^(*n))^2  >=  2(1 - 1/e) min(1, 2 n rho) / min(n x^2, 4).
```

- If `2 n rho >= 1`, this is at least `(1 - 1/e)/2 > 0.31`.
- Otherwise it is at least `4(1 - 1/e) rho/x^2`, which tends to `infinity`.
- So the HS ratio is at least `0.55` for large `m`.
- The op and rank ratios are covered by (F6).

## 3. Where `p = 2` differs

- In (S>), the HS comparison needs `eta/eps^2 -> 0`. That is the negation of the `p = 2` witness condition
  `eps^2/eta -> 0`.
- In (S<), it needs `x^2/rho -> 0`, against `rho/x^2 -> 0`.
- So the two data families exist only off `p = 2`. This matches the positive HS case of
  `classical-unitary-ratio-witnesses-amplify-to-metric-models`.

## 4. Numerical cross-check

- `experiments/schatten-p-tensor-replica-2026-09-17/check_schatten_replicas.py` computes `mu^(*n)` and `nu^(*n)`
  exactly, as the joint law of net step and flip parity, obtained by FFT of the two generating polynomials.
- It uses power-law instances of (S>) and (S<), with `p in {1, 1.5, 3, 4}`, over a geometric grid of degrees `n`.
- `output.txt` shows three things:
  - the `n = 1` ratio decreasing in `m`;
  - relator `L_p >= 0.9` wherever the element reaches `L_p >= 1`;
  - every classical ratio at least `0.99`.
- The decay of the `n = 1` ratio is slow, because the chosen exponents are small. The proof above does not rely on
  the script.
