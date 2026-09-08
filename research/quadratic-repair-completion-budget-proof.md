---
rg: 2
id: quadratic-repair-completion-budget-proof
kind: route
title: Sum the geometric defects, bound the product of padding factors, and use integrality
target: quadratic-repair-steps-complete-in-finite-dimension
requires:
  - flexible-hs-metric-controls-words-and-padding
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

## Proof

Iterate `(RB1)` from `U^(0)`, writing `e_j = e(U^(j))` and `d_j` for the
dimensions.

**Defects.**  If `e_j <= e_0 <= 1/(4A^2)` then `A sqrt(e_j) <= 1/2`, so
`e_(j+1) <= A e_j^(3/2) = (A sqrt(e_j)) e_j <= e_j / 2`.  By induction
`e_j <= 2^(-j) e_0` and every iterate stays below the threshold, so the
hypothesis applies again at each step.

**Dimensions.**  `d_(j+1) <= d_j (1 + B e_j)`, hence

```text
d_j <= d_0 prod_i (1 + B e_i) <= d_0 exp( B sum_i e_i ) <= d_0 exp(2 B e_0),
```

so `(d_j)` is a nondecreasing sequence of integers bounded above.  It is
therefore eventually constant, say `d_j = D` for `j >= J`, and for `j >= J` the
step adds nothing: `r_j = 0` and all later tuples live in `U(D)`.

**Convergence.**  For `j >= J` the metric `d_0` restricted to equal dimensions
is the normalized Hilbert-Schmidt distance (first prerequisite), and
`max_s d_0(U_s^(j+1), U_s^(j)) <= B sqrt(e_j) <= B sqrt(e_0) 2^(-j/2)` is
summable, so each `U_s^(j)` is Cauchy in `U(D)` and converges to some
`U_s^(inf)`. Closedness of the fixed-dimensional class places this tuple
in `C`. The defect is `2L`-Lipschitz in that metric (first prerequisite),
so `e(U^(inf)) = lim e_j = 0`: every word in `W` is exactly the identity.

**Movement.**  Summing over all steps, including those before `J` where the
dimension changes and the estimate is taken in the zero-padding metric, which
the first prerequisite proves is a genuine metric on tuples of all positive
dimensions,

```text
max_s d_0(U_s^(0), U_s^(inf)) <= sum_(j >= 0) B sqrt(e_j)
        <= B sqrt(e_0) sum_(j >= 0) 2^(-j/2) = B sqrt(e_0) / (1 - 2^(-1/2)),
```

which is `(RB2)`.

**The modulus.**  For `e(U) <= min(eps, 1/(4A^2))` this is
`D(U) <= 3.42 B sqrt(e(U))`.  For larger defect use the diameter of the metric:
for tuples of dimensions `d` and `D'`,

```text
d_0(U_s, W_s) = ||j(U_s) - j(W_s)||_F / sqrt(max(d, D'))
              <= (sqrt d + sqrt(D')) / sqrt(max(d, D')) <= 2,
```

so a single exact tuple anywhere in the class -- the exact locus is assumed
nonempty, as it must be for `D` to be defined -- gives `D(U) <= 2` for every
input. Put `tau=min(eps,1/(4A^2))` and
`K=max(3.42 B,2/sqrt(tau))`. Below `tau` the local bound and the
diameter bound together give `D(U)<=min(K sqrt(e(U)),2)`; above `tau`
this minimum is exactly `2`. This proves `(RB3)`. Using the unmodified
coefficient `3.42 B` globally would not follow from the local estimate.
