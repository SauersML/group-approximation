---
rg: 2
id: fpbs-tree-walk-pivotal-count-bounded-below-l2-threshold-proof
kind: route
title: Reduce to an exponentially tilted radial law, Doob-transform the radial chain to a simple walk, and compare ballot counts
target: fpbs-tree-walk-pivotal-count-bounded-below-l2-threshold
requires:
  - fpbs-l2-gap-gives-bounded-pivotal-counts
artifacts:
  - experiments/tree-pivotal-threshold-2026-09-17/tree_pivotal_counts.py
---

Notation as in the target. Write `|x|` for the distance from `e`,
`rho = 2 sqrt(d-1)/d`, `beta = d/(d-1)` and `w_k = P(|X_n| = k)`.

### Step 1. Reduction to a tilted law (part 1)

In a tree the only simple path from `e` to `v` is the geodesic. It has `|v|`
edges and lies in `B_|v|`. For `|X_n| <= n <= R`:

* `E_(n,R)` is the event that every edge of the geodesic from `e` to `X_n` is
  open;
* on that event every one of these `|X_n|` edges is open and pivotal, and no
  other edge is pivotal.

So `N_(n,R) = |X_n|` on `E_(n,R)`. Since the walk and the percolation are
independent, `P(E_(n,R) | |X_n|=k) = p^k`, and

```text
E_p[N_(n,R) | E_(n,R)] = sum_k k w_k p^k / sum_k w_k p^k.        (1.1)
```

This does not depend on `R>=n` and is at most `n`. It is the mean of `k` under
the law proportional to `w_k p^k`, and its `p`-derivative is `Var(k)/p >= 0`
under that law. This proves part 1.

### Step 2. The bounded regime (part 2)

By Step 1, `tau_p(u,v) = p^(d(u,v))`. Apply the Schur test with
`h(v) = (d-1)^(-|v|/2)`. The test: if a symmetric nonnegative kernel `K`
satisfies `sum_v K(u,v) h(v) <= M h(u)` for all `u`, with `h>0`, then
`|<f,Kg>| <= M ||f|| ||g||`. This follows from Cauchy–Schwarz applied to
`K(u,v)|f(u)||g(v)| = (K h(v)/h(u))^(1/2) |f(u)| (K h(u)/h(v))^(1/2) |g(v)|`.

Fix `u` and a vertex `v` with `d(u,v) = m`. The geodesic from `u` to `v` first
moves `i` steps toward `e`, with `0 <= i <= min(m,|u|)`, and then `m-i` steps
away from `e`. So `|v| = |u| + m - 2i`.

* For fixed `(m,i)` there are at most `d (d-1)^(m-i-1) <= (3/2)(d-1)^(m-i)`
  such `v` when `m>i`, and exactly one when `m=i`.
* `h(v)/h(u) = (d-1)^(-(m-2i)/2)`.

Hence

```text
sum_{d(u,v)=m} h(v) <= (3/2) sum_{i=0}^{m} (d-1)^(m-i) (d-1)^(-(m-2i)/2) h(u)
                     = (3/2)(m+1)(d-1)^(m/2) h(u),
```

and with `x = p sqrt(d-1) < 1`,

```text
sum_v p^(d(u,v)) h(v) <= (3/2) sum_m (m+1) x^m h(u) = 3/(2(1-x)^2) h(u).
```

So `||T_p|| <= 3/(2(1-x)^2)`. Theorem 4.1 of
`research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`, recorded
as `fpbs-l2-gap-gives-bounded-pivotal-counts`, reads verbatim:
"Then for all `n>=1` and `R>=n`,
`E_p[N_(n,R) | E_(n,R)] <= 2 d ||T_p||_(2->2)^2`."
It therefore gives `E_p[N|E] <= 2d (3/(2(1-x)^2))^2 = 9d/(2(1-x)^4)`. This
proves part 2.

### Step 3. Doob transform of the radial chain

`|X_n|` is a Markov chain on `{0,1,2,...}`:

* from `0` it moves to `1` with probability `1`;
* from `k>=1` it moves to `k+1` with probability `(d-1)/d` and to `k-1` with
  probability `1/d`.

Put `g(k) = (d-1)^(-k/2)`. For `k>=1`,

```text
(d-1)/d = (rho/2) g(k)/g(k+1)   and   1/d = (rho/2) g(k)/g(k-1),
```

and `1 = beta (rho/2) g(0)/g(1)`.

A radial path `gamma = (0 = y_0, ..., y_n = k)` is a `+-1` lattice path that
stays `>= 0`. Let `L(gamma) = #{0 <= i < n : y_i = 0}`. The products telescope,
so the probability of `gamma` is `(rho/2)^n beta^(L(gamma)) g(0)/g(k)`. Hence

```text
w_k = rho^n (d-1)^(k/2) sigma_k(n),   sigma_k(n) := 2^(-n) sum_{gamma: 0 -> k} beta^(L(gamma)),   (3.1)
```

and by (1.1), with `x = p sqrt(d-1)`,

```text
E_p[N_(n,R) | E_(n,R)] = sum_k k x^k sigma_k(n) / sum_k x^k sigma_k(n).   (3.2)
```

**Lemma 3.1.** `sigma_k(n) <= beta` for all `k, n`.

*Proof.* First take `k=0`. On `T_d`, let `H(v) = g(|v|)` and let `P` be the
walk operator. For `v != e`, `PH(v) = rho H(v)` by the identities above. At
`e`, `PH(e) = (d-1)^(-1/2) = (d/(2(d-1))) rho H(e) <= rho H(e)`. So
`PH <= rho H` pointwise, and `P^n H <= rho^n H` because `P` is positive. Then
`mu^n(e) H(e) <= (P^n H)(e) <= rho^n H(e)`, so `sigma_0(n) = mu^n(e)/rho^n <= 1`
by (3.1).

Now take `k>=1`. Reversing paths `y_i -> y_(n-i)` is a bijection from paths
`0 -> k` to paths `k -> 0`. It carries `L` to `#{0 < i <= n : y'_i = 0}`.
Split a reversed path at its first zero `t`:

* the prefix is a first-passage path from `k` to `0` of length `t`, with no
  zeros counted;
* the suffix is a path `0 -> 0` of length `n-t`. Its zeros at positions
  `0..n-t` number `L(suffix)+1`.

So `sigma_k(n) = beta sum_t f_k(t) sigma_0(n-t)`, where `f_k(t)` is the
probability that simple random walk on `Z` started at `k` first hits `0` at
time `t`. Since `sum_t f_k(t) <= 1` and `sigma_0 <= 1`, `sigma_k(n) <= beta`.
QED

### Step 4. The linear regime (part 3)

Let `x>1`, `delta = min(ln(x)/2, 1/2)`, `eps = delta/4` and `n>=4`. Under the
law `pi_n(k)` proportional to `x^k sigma_k(n)`, (3.2) is the mean of `k`.

*Numerator.* By Lemma 3.1,
`sum_{k<eps n} x^k sigma_k(n) <= beta (n+1) x^(eps n)`.

*One large term.* Choose `k*` with `k* = n (mod 2)` and
`delta n <= k* <= delta n + 2`. Then `k* <= n`, since `delta <= 1/2` and
`n >= 4`. Put `u = (n+k*)/2`. Since `beta >= 1`, `sigma_(k*)(n)` is at least
`2^(-n)` times the number of `+-1` paths `0 -> k*` of length `n` that stay
`>= 0`. By the reflection principle this number is

```text
C(n,u) - C(n,u+1) = C(n,u) (k*+1)/(u+1) >= C(n,u)/(n+1).
```

Next, `C(n,u) >= 2^(n H(u/n))/(n+1)`, where `H` is the binary entropy in bits.
Write `delta' = k*/n`. Using `ln(1+s) <= s`,

```text
1 - H((1+delta')/2) = [(1+delta')ln(1+delta') + (1-delta')ln(1-delta')]/(2 ln 2) <= delta'^2/ln 2.
```

So `2^(-n) C(n,u) >= e^(-n delta'^2)/(n+1)`. Also
`n delta'^2 <= n delta^2 + 4 delta + 4/n <= n delta^2 + 3`. Therefore

```text
x^(k*) sigma_(k*)(n) >= x^(delta n) e^(-n delta^2 - 3) / (n+1)^2.
```

*Comparison.* Combining the two bounds,

```text
pi_n(k < eps n) <= beta e^3 (n+1)^3 exp( n [ (eps - delta) ln x + delta^2 ] ).
```

We have `(eps-delta) ln x = -(3/4) delta ln x`, and `delta^2 <= delta ln(x)/2`
because `delta <= ln(x)/2`. So the exponent is at most `-n delta ln(x)/4`, and

```text
E_p[N_(n,R)|E_(n,R)] >= eps n pi_n(k >= eps n)
                      >= eps n (1 - beta e^3 (n+1)^3 exp(-n delta ln(x)/4)).
```

This proves part 3. QED

### Remarks

* At `p = p_*` (`x=1`), Lemma 3.1 alone does not decide boundedness. That
  would need the local limit order `mu^n(e) ~ rho^n n^(-3/2)`, which is not
  proved here. The script shows growth of order `sqrt(n)`.
* The script checks (1.1), `mu^n(e) <= rho^n` and Lemma 3.1 exactly for
  `d=3`, `n <= 320`.
