---
rg: 2
id: invariant-norm-ratio-witnesses-localize-hyperlinear-proof
kind: route
title: Pin the involution's spectrum to plus or minus one, bound every generator's far mass by normal generation, and cut the model down to the far spectral subspace
target: invariant-norm-ratio-witnesses-localize-hyperlinear
requires:
  - thompson-v-finitely-presented-infinite-simple
artifacts:
  - experiments/involution-far-mass-localization-2026-09-17/check_localization.py
  - experiments/involution-far-mass-localization-2026-09-17/output.txt
---

Everything below is finite-dimensional linear algebra. The only import is the classical fact that `V` is finitely
presented, infinite and simple, which is used in part (C). `||.||` is the operator norm, and "for large `n`" means for
all but finitely many `n`.

## 1. Far mass

**Lemma 1.** Let `x, y, z in U(d)` with `x = yz`, `||y - I|| <= delta` and `rank(z - I) <= k`. Then `x` has at most `k`
eigenvalues `w` with `|w - 1| > delta`.

*Proof.* On `ker(z - I)`, which has codimension at most `k`, `(x - I)v = (y - I)v`, so `||(x - I)v|| <= delta ||v||`.
`x` is normal, so `A = (x - I)^*(x - I)` has eigenvalues `|w_i - 1|^2`. The quadratic form of `A` is at most `delta^2`
on a subspace of codimension at most `k`. By Courant--Fischer, at most `k` eigenvalues of `A` exceed `delta^2`. QED.

Conversely, the spectral splitting gives such a factorization with `k = d F_delta(x)`. Write `x = x_B x_S`, where
`x_B = xP + (I - P)` and `x_S = P + x(I - P)`, and `P` is the spectral projection of `x` for `{|w - 1| > delta}`. Then
`rank(x_B - I) <= rank P` and `||x_S - I|| <= delta`, and the two factors commute.

**Corollary 2.** For `x, y in U(d)`:

1. `F_(delta1 + delta2)(xy) <= F_delta1(x) + F_delta2(y)`;
2. `F_delta(g x g^-1) = F_delta(x)` and `F_delta(x^-1) = F_delta(x)`;
3. `F_delta(x) = 0` if `||x - I|| <= delta`.

*Proof of 1.* Split `x = y1 z1` and `y = y2 z2` spectrally at `delta1` and `delta2`. Then

```text
xy = (y1 y2)(y2^-1 z1 y2 z2),
```

with `||y1 y2 - I|| <= delta1 + delta2`. Since `ab - I = a(b - I) + (a - I)`,
`rank(y2^-1 z1 y2 z2 - I) <= rank(z1 - I) + rank(z2 - I)`. Now apply Lemma 1. Items 2 and 3 are clear from the
spectrum. QED.

By induction, `F_(sum delta_i)(x_1 ... x_m) <= sum_i F_(delta_i)(x_i)`.

## 2. Unitarily invariant norms

Let `N` be a unitarily invariant norm on `M_d`.

- **(N1)** `N(C X C') <= ||C|| ||C'|| N(X)`. A contraction `C` is an average of two unitaries. Take the polar form
  `C = W|C|` with `W` unitary, and put `T = |C| + i(I - |C|^2)^(1/2)`, which is unitary. Then `|C| = (T + T^*)/2`, so
  `C = (WT + WT^*)/2`. Now apply the triangle inequality.
- **(N2)** Projections of equal rank are unitarily conjugate, so `phi(k) := N(P)` for `rank P = k` is well defined, and
  `phi(0) = 0`.
  - `phi` is nondecreasing: nested projections satisfy `P_k = P_k P_(k+1)`, then use (N1).
  - `phi(j)/j` is nonincreasing for `j >= 1`. Let `e_1, ..., e_(k+1)` be an orthonormal basis of the range of `P_(k+1)`.
    Then `k P_(k+1) = sum_j (P_(k+1) - e_j e_j^*)`, a sum of `k + 1` rank-`k` projections. So
    `phi(k+1) <= ((k+1)/k) phi(k)`.
  - Consequently `phi(k') >= min(1, k'/k) phi(k)` for all `k, k' >= 1`.
- **(N3)** The length `l(x) = N(x - I)` on `U(d)` is conjugation invariant and symmetric, because
  `x^-1 - I = -x^-1(x - I)`. It is subadditive, because `xy - I = x(y - I) + (x - I)`.
## 3. Part (A)

Fix the data of (A). Drop the index `n` when it is clear, and write `x = sigma(U_n)` and `eta = eta_n`.

**Expressions in F(S).** `sigma` has order `2` in `G`, so in `F(S)`

```text
sigma^2 = prod_(i=1)^(M_0) g_i r_i^(+-1) g_i^(-1)        (g_i in F(S), r_i in R).
```

`G` is the normal closure of `sigma`. So `F(S) = <<sigma>> <<R>>`, and each `s in S` has an expression

```text
s = prod_(j=1)^(N_s) h_j sigma^(+-1) h_j^(-1) * prod_(k=1)^(M_s) g'_k r'_k^(+-1) g'_k^(-1).
```

Fix these finitely many expressions once and for all. Put `N = max_s N_s` and `K = |S| (N + 1)`. Only finitely many
relators occur in them, so (FM) gives `F_delta(r(U_n)) = o(eta_n)` uniformly over those relators, for each fixed
`delta`.

**Step 1 (the involution sits on plus or minus one).** Let `z` be an eigenvalue of `x` with `Re z >= 0` and
`|z - 1| > delta`. Then `|z + 1|^2 = 2 + 2 Re z >= 2`, so `|z^2 - 1| = |z - 1| |z + 1| > delta`. The eigenvalues of `x^2`
are the squares of those of `x`, with multiplicity. Hence

```text
F_delta(x) <= eta + F_delta(x^2) <= eta + sum_i F_(delta/M_0)(r_i(U)) = eta + o(eta)
```

by Corollary 2 applied to the expression of `sigma^2`. Also `|z - 1|^2 = 2 - 2 Re z`, so `|z - 1| > sqrt 2` exactly when
`Re z < 0`. Thus `F_(sqrt 2)(x) = eta`.

**Step 2 (scale-free generator bound).** Apply Corollary 2 to the expression of `s`, splitting `delta` equally among its
`N_s + M_s` factors. Conjugation and inversion do not change far mass, so for every fixed `delta > 0`

```text
F_delta(s(U_n)) <= N_s F_(delta/(N_s+M_s))(x) + o(eta) <= N eta_n + o(eta_n).
```

The constant `N` does not depend on `delta`.

**Step 3 (a vanishing threshold).** By Step 2, for each `k >= 1` there is `n_k` with
`F_(1/k)(s(U_n)) <= (N + 1) eta_n` for all `s in S` and all `n >= n_k`. Take `n_1 < n_2 < ...` and put `delta_n = 1/k`
for `n_k <= n < n_(k+1)`. Then `delta_n -> 0` and, for `n >= n_1`,

```text
F_(delta_n)(s(U_n)) <= (N + 1) eta_n     for every s in S.                          (3)
```

**Step 4 (localization; this is the death step for witnesses).** For `s in S` let `P_s` be the spectral projection of
`s(U_n)` for `{w : |w - 1| > delta_n}`. By (3), `rank P_s <= (N + 1) eta_n d_n`. Let `E = E_n` be the span of the ranges of
all `P_s`, so

```text
D := dim E <= K eta_n d_n.
```

Split each generator spectrally, as in Section 1:

```text
s(U) = s_B s_S,    s_B = s(U) P_s + (I - P_s),    s_S = P_s + s(U)(I - P_s),    ||s_S - I|| <= delta_n.
```

`s_B` is unitary. `s_B - I = (s(U) - I) P_s` vanishes on `(range P_s)^perp`, which contains `E^perp`. So `s_B` fixes
`E^perp` pointwise, and being unitary it maps `E` onto `E`. Write `s_B = shat (+) I` on `E (+) E^perp`, with
`shat in U(E)`, and let `Uhat = Uhat_n = (shat)_(s in S)`. Write `U_B = (s_B)_s`.

**Step 5 (words).** For unitaries, `||a_1 ... a_m - b_1 ... b_m|| <= sum_i ||a_i - b_i||`. Also
`||s(U) - s_B|| = ||s_B (s_S - I)|| <= delta_n`, and the same holds for inverses. So for every word `w` of length `m`

```text
||w(U) - w(U_B)|| <= m delta_n,        w(U_B) = w(Uhat) (+) I_(E^perp).               (5)
```

In particular `w(U) = w(U_B) y_w` with `||y_w - I|| <= m delta_n`, and `w(U_B)` and `w(Uhat)` have the same
eigenvalues other than `1`, with the same multiplicities.

**Step 6 (the model on E).**

- *Separation of sigma.* Let `m` be the length of `sigma`. For `n` large, `m delta_n <= sqrt 2 - 1`. By Corollary 2,
  (5) and Step 1,

  ```text
  eta = F_(sqrt 2)(sigma(U)) <= F_1(sigma(U_B)) + F_(m delta_n)(y_sigma) = F_1(sigma(U_B)).
  ```

  So `sigma(Uhat)` has at least `eta d` eigenvalues `w` with `|w - 1| > 1`. In particular `D >= eta d >= 1`, and

  ```text
  l_2(sigma(Uhat))^2 = (1/D) sum_w |w - 1|^2 >= eta d / D >= 1/K.
  ```

- *Relators.* Fix `r in R` of length `m_r` and `delta' > 0`. For `n` large, `m_r delta_n <= delta'/2`. Then by (5) and
  Corollary 2, `F_(delta')(r(U_B)) <= F_(delta'/2)(r(U)) = o(eta)`. So the number of eigenvalues `w` of `r(Uhat)` with
  `|w - 1| > delta'` is `o(eta d)`, which is `o(D)` because `D >= eta d`. Every eigenvalue has `|w - 1| <= 2`, so

  ```text
  l_2(r(Uhat))^2 <= delta'^2 + 4 o(1).
  ```

  Since `delta'` is arbitrary, `l_2(r(Uhat_n)) -> 0`.

The two displays are the conclusion of (A). The two facts that `D <= K eta d` and that `D >= eta d` are the whole point. The
relator far mass is `o(eta d)` and `sigma`'s far mass is at least `eta d`. So both are measured against the same scale
`eta d`, and on `E` that scale becomes the normalization.

**Step 7 (ultraproduct).** Fix a nonprincipal ultrafilter `omega`. `l_2` is a bi-invariant length on each `U(D_n)`, so
`N_omega = {(u_n) : lim_omega l_2(u_n) = 0}` is a normal subgroup of `prod_n U(D_n)`, and the quotient is the unitary
group of the tracial ultraproduct `prod_omega M_(D_n)`. The assignment `s -> [(shat_n)]` kills every `r in R` by Step 6,
so it defines a homomorphism `pi` of `G`. By Step 6, `lim_omega l_2(sigma(Uhat_n))^2 >= 1/K`, so `pi(sigma) != 1`. If `G`
is simple, `ker pi` is a proper normal subgroup, hence trivial, and `G` embeds in the unitary group of a tracial
ultraproduct of matrix algebras. That is hyperlinearity. QED (A).

## 4. Part (B)

Now `R` is finite and `G` is simple, so `sigma != 1` normally generates `G`. Put `rho = max_r l(r(U_n))` and
`lambda = l(a(U_n)) > 0`, so `rho = o(lambda)` by (W). Let `x = sigma(U_n)`, let `P` be its spectral projection for
`{Re z < 0}`, and let `k = rank P = eta d`. Write `phi` for the function of (N2) for `N_d`.

- **B1.** `a` lies in `<<sigma>> <<R>>`, so `a = prod_(j=1)^(N_2) h_j sigma^(+-1) h_j^(-1) * (M_a conjugates of relators)`.
  By (N3), `lambda <= N_2 l(x) + M_a rho`. For `n` large, `M_a rho <= lambda/2`, so `l(x) >= lambda/(2 N_2)`.
- **B2.** By the expression of `sigma^2` and (N3), `l(x^2) <= M_0 rho`.
- **B3.** Split `x - I = (x - I)P + (x - I)(I - P)`.
  - By (N1), `N((x - I)P) <= ||x - I|| N(P) <= 2 phi(k)`.
  - Let `g(z) = (z + 1)^(-1)` for `Re z >= 0` and `g(z) = 0` otherwise. On the spectrum of `x` with `Re z >= 0` we have
    `|z + 1| >= sqrt 2`, so `||g(x)|| <= 1`. By functional calculus `(x - I)(I - P) = (x^2 - I) g(x)`. By (N1) and B2,
    `N((x - I)(I - P)) <= M_0 rho`.

  So `lambda/(2 N_2) <= 2 phi(k) + M_0 rho`. For `n` large, `phi(k) >= lambda/(5 N_2) > 0`. Since `phi(0) = 0`, this
  gives `k >= 1`, that is `eta_n > 0`.
- **B4.** Fix `r in R` and `delta > 0`. Let `Q` be the spectral projection of `r(U_n)` for `{|w - 1| > delta}`, with
  `k_r = rank Q`. Let `h(w) = (w - 1)^(-1)` for `|w - 1| > delta` and `h(w) = 0` otherwise. Then `Q = (r(U) - I) h(r(U))`
  and `||h(r(U))|| <= 1/delta`. By (N1), `phi(k_r) <= rho/delta`.
  - If `k_r >= k`, then by (N2) `phi(k_r) >= phi(k) >= lambda/(5 N_2)`. That contradicts `rho/delta = o(lambda)` for `n`
    large.
  - So `k_r < k`. If `k_r >= 1`, (N2) gives `(k_r/k) phi(k) <= phi(k_r) <= rho/delta`. Hence
    `k_r / k <= 5 N_2 rho / (delta lambda) -> 0`. This also holds trivially when `k_r = 0`.

  Therefore `F_delta(r(U_n)) = k_r/d = (k_r/k) eta_n = o(eta_n)`.

B3 and B4 are (FM) for `sigma`, and (A) applies. QED (B).

The norm enters only through (N1) and (N2). They let a single number `phi(k)`, the norm of a rank-`k` projection, compare
the far mass of `sigma` with that of each relator in one common unit. No hypothesis on how `N_d` depends on `d` is
needed, because each step uses one `d` at a time.

## 5. Part (C)

`V` is finitely presented, infinite and simple (`thompson-v-finitely-presented-infinite-simple`). The homeomorphism of
Cantor space `{0,1}^N` that swaps the first letter, `0w <-> 1w`, is an element of `V` of order `2`. Any unitarily
invariant norms `N_d` give lengths `l = N_d(. - I)` to which (B) applies. So a ratio witness (W) for `V` in any such
length makes `V` hyperlinear.

*Converse for normalized Schatten `p < infinity`.* Let `l_p(u) = (tr |u - I|^p / d)^(1/p)`. For a unitary `u`, `u - I`
is normal with singular values `t_i = |w_i - 1| <= 2`. By the power-mean inequality `l_p` is nondecreasing in `p`. From
`t^p <= 2^(p-2) t^2` for `p >= 2`, and `t^2 <= 2^(2-p) t^p` for `p <= 2`,

```text
l_2 <= l_p <= 2^((p-2)/p) l_2^(2/p)   (p >= 2),        l_p <= l_2 <= 2^((2-p)/2) l_p^(p/2)   (p <= 2).
```

So `l_p -> 0` exactly when `l_2 -> 0`, and a lower bound on one gives a lower bound on the other. If `V` is
hyperlinear, there are tuples with `l_2(r(U_n)) -> 0` for the finitely many relators and `l_2(a(U_n)) >= c > 0`. These
form an `l_p` ratio witness. For the operator norm the converse would be "hyperlinear implies MF" for `V`, and nothing
is claimed about it.

