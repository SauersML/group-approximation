---
rg: 2
id: bs12-fourier-monomial-holonomy-rigidity-proof
kind: route
title: Pair the exact cocycle equation with translated Bernoulli B_1 cokernel vectors averaged over each doubling cycle
target: bs12-fourier-monomial-corrections-need-equal-cycle-holonomies
requires: []
artifacts:
  - experiments/bs12-weighted-shift-2026-09-17/fourier_monomial_obstruction.py
---

Lane proof (swarm-0917-w14, 2026-09-19), not reviewed; self-contained and
elementary.  Notation is that of the target.

**Step 1: the cocycle equation.**  For `(C, Z)` in class F,

```text
C Z C^* f_(2m) = e^(i(t_m + a_(m-1) - a_m)) f_(2m-2),
Z^2 f_(2m)     = e^(i(t_(2m) + t_(2m-1))) f_(2m-2).
```

Since `m -> 2m` is a bijection of `Z/N`, the pair is exact iff

```text
(T t)_m := t_(2m) + t_(2m-1) - t_m  =  a_(m-1) - a_m  (mod 2 pi)   for all m.
```

Under the lift hypothesis, both sides have absolute value below `2 pi`
after the difference is taken, so the integer correction vanishes and
`T t = grad a` holds over `R`, where `(grad a)_m = a_(m-1) - a_m`.  Summing
over `m`, the left side sums to `2 sum t - sum t` and the right side to `0`.
So `sum t = 0`, and then `Z^N = e^(i sum t) D^N = 1`.  The spectrum of `Z`
is therefore the set of `N`-th roots of unity, each with multiplicity one.

**Step 2: the Bernoulli cokernel vector.**  For `m` in `Z/N` let
`r(m) in {1,...,N}` be its representative, and put
`y_m = r(m)/N - (N+1)/(2N)`.  This is the periodic Bernoulli function
`B_1`, sampled with a `1/(2N)` offset.  Then

```text
y_(2i) = y_i + y_(i+h)        for all i in Z/N.                      (B)
```

To check (B), write `r = r(i)`.  If `r <= (N-1)/2`, then `r(2i) = 2r` and
`r(i+h) = r+h`.  If `r >= h`, then `r(2i) = 2r-N` and `r(i+h) = r+h-N`.  In
both cases (B) reduces to `2h = N+1`.  The script also checks (B) in exact
rationals for all odd `N < 400`.

Next, (B) says `T^T y = 0`.  Indeed, `(T^T y)_j = y_(hj) + y_(h(j+1)) - y_j`,
and `h(2i) = i`, `h(2i+1) = i+h`.

**Step 3: cycle averages.**  Let `(tau_k y)_m = y_(m-k)`, and let `L` be the
operator `(L z)_(2i) = z_i + z_(i+h)`.  Relation (B) is `L y = y`.
Substituting `i -> i - kh` gives `L(tau_(kh) y) = tau_k y`, since
`2kh = k`.  So `L` maps `tau_j y` to `tau_(2j) y`.  For a doubling cycle
`gamma`, the average `y^gamma = |gamma|^(-1) sum_(k in gamma) tau_k y` is
therefore `L`-fixed, and `T^T y^gamma = 0`.

**Step 4: pairing.**  Pair `T t = grad a` with `y^gamma`:

```text
0 = sum_m y^gamma_m (a_(m-1) - a_m) = sum_m a_m (y^gamma_(m+1) - y^gamma_m).
```

From the definition, `y_(m+1) - y_m = 1/N - [m = 0]`, so
`y^gamma_(m+1) - y^gamma_m = 1/N - 1_gamma(m)/|gamma|`.  Hence
`0 = mean(a) - avg_gamma(a)`, which is (HR).  The weights `t` dropped out
at the first equality.

**Step 5: distances.**  Take lifts `b_m in (-pi, pi]` of `a_m - g_m` and
`t_m in (-pi, pi]`.  Then `||C - A_s|| = max_m |e^(i b_m) - 1|` and
`||Z - D|| = max_m |e^(i t_m) - 1|`.  If both are at most `eps <= 1/2`,
then `|b|, |t| <= 2 arcsin(1/4) < 0.506`.  With `a = g + b` and `N > 4s`,
the lift bound of item 1 is at most `4 pi s/N + 1.012 + 1.518 < 2 pi`
(and at most `1 + 1.012 + 1.518` in item 3).  By (HR), for any two cycles,
`avg_gamma b - avg_gamma' b = avg_gamma' g - avg_gamma g`, and the left side
is at most `2 max|b|` in absolute value.  So `max|b| >= beta`, where
`beta` is half the spread of the cycle averages of `g`, and
`eps >= 2 sin(beta/2)`.

For `A_s`: the cycle `{0}` has average `g_0 = 2s`.  The global mean of `g`
is `0` and is a convex combination of cycle averages, so some cycle has
average at most `0`, and `beta >= s`.  If `3 | N`, the cycle
`{N/3, 2N/3}` has average `2s cos(2 pi/3) = -s`, so `beta >= 3s/2`.
Finally, `||W - A_s|| = max|e^(i g_m) - 1| <= 2 sin s`.  QED.
