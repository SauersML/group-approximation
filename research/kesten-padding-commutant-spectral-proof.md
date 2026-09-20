---
rg: 2
id: kesten-padding-commutant-spectral-proof
kind: route
title: Compute the averaging moments as return probabilities and pad the lift with an idle phase corner
target: kesten-padding-blinds-commutant-spectral-sizes
requires: []
---

Notation as in the target. Write `v_i = sigma_n(s_i)`. Normalizing sequences satisfy `f_n >= 1`.
Also `d_n -> infinity` along `omega`: `sigma(Gamma)` is an infinite family of pairwise
`tau`-orthogonal unitaries, which a bounded-dimensional ultraproduct cannot contain.

## Step 0: the quadratic form

For a unitary `v` and `x in H_n`, `||v x v^* - x||_2 = ||v x - x v||_2 = ||[v,x]||_2`, and
`(Ad v)^* = Ad v^*`. So `Phi_n` is self-adjoint with `||Phi_n|| <= 1`, and

```text
<(1 - Phi_n) x, x> = (1/2m) sum_i < (2 - Ad v_i - Ad v_i^*) x, x >
                   = (1/2m) sum_i ||Ad v_i x - x||_2^2
                   = (1/4m) sum_(s in S) ||[sigma_n(s), x]||_2^2,
```

using `||[v^*, x]||_2 = ||[v, x]||_2`. By Courant--Fischer, `N_n(eta)` is the largest dimension of
a subspace on which this form is at most `eta ||x||_2^2`. The same computation, with
`lambda(s_i)` acting on `l^2(Gamma)`, gives
`<(1 - lambda(mu_S)) x, x> = (1/2m) sum_i ||lambda(s_i) x - x||^2`.

## Step 1: SK1

`Ad(sigma_n(u) v_i sigma_n(u)^-1) = Ad sigma_n(u) Ad v_i Ad sigma_n(u)^-1 = T_n^-1 Ad v_i T_n`,
and likewise for the adjoints. Summing gives `Phi^B_n = T_n^-1 Phi_n T_n`. The map `T_n` is
unitary on `H_n`, because `Ad` of a unitary preserves `tr(y^* x)`. So the spectra agree with
multiplicity, and `N^B_n = N_n` for every lift and every `n`.

## Step 2: SK2, moments

For a unitary `v` in `M_d`, `Ad v = v ⊗ conj(v)` on `C^d ⊗ C^d = H_n`, so
`Tr_H(Ad v) = |Tr v|^2`. Also `Ad` is multiplicative:
`Ad sigma_n(g_1) ... Ad sigma_n(g_k) = Ad(sigma_n(g_1) ... sigma_n(g_k))`, and
`sigma_n(g_1) ... sigma_n(g_k)` lifts `sigma(g_1 ... g_k)`. Hence

```text
d_n^-2 Tr_H( Ad sigma_n(g_1) ... Ad sigma_n(g_k) ) = | tr sigma_n(g_1 ... g_k) |^2
   -> | tau(sigma(g_1 ... g_k)) |^2 = [g_1 ... g_k = 1 in G] = tau_(L(G))( lambda(g_1) ... lambda(g_k) ),
```

by trace preservation. Linear extension gives the joint-distribution statement. In particular,
expanding `Phi_n^k` over letter sequences in `S^k`:

```text
lim_omega d_n^-2 Tr_H(Phi_n^k) = (2m)^-k #{ words of length k in S equal to 1 in Gamma }
                               = < lambda(mu_S)^k delta_e, delta_e > = integral t^k d mu_(Gamma,S)(t).
```

All the measures involved live on `[-1, 1]`. By Weierstrass, moment convergence is weak
convergence of the normalized spectral measures of `Phi_n` to `mu_(Gamma,S)`. So
`d_n^-2 N_n(eta) -> mu_(Gamma,S)([1-eta, 1])` at every continuity point.

**No mass at 1 for infinite `Gamma`.** Suppose `lambda(mu_S) x = x` in `l^2(Gamma)`. Then
`||x||^2 = <lambda(mu_S) x, x> = (1/2m) sum_(s in S) Re <lambda(s) x, x>`. This is an average of
`2m` numbers, each at most `||x||^2` by Cauchy--Schwarz. Equality forces `lambda(s) x = x` for every `s`, so
`x` is constant on `Gamma`, and hence `x = 0`. So `mu({1}) = ||P_1 delta_e||^2 = 0`, and
`mu([1-eta, 1]) -> 0` as `eta -> 0`.

## Step 3: SK2 under (T)

Let `kappa` be a Kazhdan constant for `(Gamma, S)`, with `Gamma` infinite. Then `l^2(Gamma)` has
no nonzero invariant vector, so for every `x`,
`max_(s in S) ||lambda(s) x - x|| >= kappa ||x||`. Since
`||lambda(s_i^-1) x - x|| = ||lambda(s_i) x - x||`, the maximum is attained at some `s_i`. By
Step 0:

```text
<(1 - lambda(mu_S)) x, x> >= (1/2m) kappa^2 ||x||^2 = c ||x||^2.
```

So `spec lambda(mu_S) ⊆ [-1, 1-c]`, and `mu_(Gamma,S)` is supported in `[-1, 1-c]`.

Fix `eta < c`. Let `h` be continuous on `[-1, 1]`, equal to 0 on `[-1, 1-c]`, equal to 1 on
`[1-eta, 1]`, and linear in between. Then `0 <= 1_[1-eta,1] <= h`, so with
`E_n = 1_[1-eta,1](Phi_n)`:

```text
d_n^-2 Tr_H(E_n) <= d_n^-2 Tr_H h(Phi_n) -> integral h d mu_(Gamma,S) = 0.
```

For `||Y_n|| <= 1`, `|Tr_H(E_n Y_n)| = |Tr_H(E_n Y_n E_n)| <= Tr_H(E_n)`, so the limit is 0. The
`B` side follows by SK1. Finally, if `lim_omega f_n/d_n^2 = a > 0`, then
`N_n/f_n = (N_n/d_n^2)(d_n^2/f_n) -> 0 * (1/a) = 0`. The case `a = +infinity` is included.

## Step 4: SK3, padding

Let `r` be the diagonal unitary `diag(e^(i a / k))`, `a = 1..k`, in `U(k)` with `k = k_n`. Define
the lift on `C^(d_n + k_n)`:

```text
sigma'_n(s_i) = v_i ⊕ r   (every i),        sigma'_n(u) = sigma_n(u) ⊕ 1_k.
```

This is a free-group homomorphism, and `sigma'_n(w) = sigma_n(w) ⊕ r^(e(w))` for every word `w`,
where `e(w)` is the exponent sum of the letters `s_i`.

**Same limit.** Let `p_n = 1_(d_n) ⊕ 0`. Then `||1 - p_n||_2^2 = k_n/(d_n + k_n) -> 0`, so
`p = 1` in `M'^omega = prod_omega M_(d_n + k_n)`. The map `x -> p x p` is therefore a
`*`-isomorphism `M'^omega -> prod_omega p_n M_(d_n + k_n) p_n = M^omega`. It preserves traces,
because `(d_n + k_n)^-1 Tr(p_n x p_n) = (d_n/(d_n + k_n)) tr(x_n) -> tr(x_n)` for bounded `x`.
It sends `sigma'(w)` to `(sigma_n(w))_n = sigma(w)`. So `sigma'` is a trace-preserving
homomorphism of `G`, conjugate to `sigma` by this isomorphism. Its commutants, their conjugates
and their Wold shifts correspond to `A`, `B` and `D`.

**Extra eigenvalues.** Every `Ad(a ⊕ b)` preserves the four blocks of `M_(d+k)` and acts on the
lower-right block `M_k` by `Ad b`. So `Phi'_n` is block diagonal. Its upper-left block is
`Phi_n`, and its lower-right block is `(1/2)(Ad r + Ad r^*)`. On the matrix unit `e_ab`,
`Ad r e_ab = e^(i(a-b)/k) e_ab`, so `e_ab` is an eigenvector with eigenvalue `cos((a-b)/k)`.
Since `|a-b|/k < 1 < pi`, we have `cos((a-b)/k) >= 1 - eta` if and only if
`|a-b| <= y k`, where `y = arccos(1-eta) in (0, pi/2]`.

- If `y >= 1`, all `k^2` pairs qualify.
- Otherwise put `t = floor(y k)`. The number of qualifying pairs is
  `k + 2 sum_(j=1)^t (k-j) = g(t) + k - t`, with `g(t) = 2tk - t^2`.
  - `g` is increasing on `[0, k]`.
  - `0 <= yk - t < 1`.
  - So `g(yk) - g(t) <= (yk - t)(2k) < 2k`.
  - Hence the count is at least `g(yk) - 2k = k^2 (2y - y^2) - 2k`.

Eigenvalue counts of a block-diagonal operator add. So
`N'_n(eta) >= N_n(eta) + k^2 (2x - x^2) - 2k` with `x = min(1, y)`, and
`N'^B_n = N'_n` by SK1 applied to the lift `sigma'`.

**Choice of `k_n`.** Suppose `lim_omega f_n/d_n^2 = 0`, and take
`k_n = ceil((f_n d_n^2)^(1/4))`. Then:
- `k_n/d_n <= (f_n/d_n^2)^(1/4) + 1/d_n -> 0`.
- `k_n^2/f_n >= (d_n^2/f_n)^(1/2) -> infinity`.
- `k_n >= d_n^(1/2) -> infinity`, since `f_n >= 1`.

For fixed `eta > 0` we have `2x - x^2 > 0`, so
`N'_n(eta)/f_n >= (k_n^2 (2x - x^2) - 2 k_n)/f_n -> infinity`. That is SK3.

## Step 5: the death of the transcription

Along `omega`, `lim f_n/d_n^2` is either positive (possibly infinite) or 0.

- **Positive.** By Steps 2 and 3, every count or trace functional of the near-1 spectral
  projections of `Phi_n` or `Phi^B_n` is, at this scale, a functional of `(L(G), tau)` that does
  not involve `sigma`. It vanishes when `eta < c`.
  - A strict increase `nu^B > nu^A` is then impossible: both sides are 0 near eigenvalue 1, and
    equal for every `eta` by Step 1.
  - Away from eigenvalue 1 they are Kesten values, which never mention `u` or `D`.
- **Zero.** Take any argument deriving a contradiction from `D != 0` through the inequality chain
  "containment `B ⊇ A` plus conjugation equality forces equality".
  - It needs `nu^A(eta) < infinity` at some `eta`: finite quantities cannot be compared
    strictly otherwise.
  - Step 4 gives, for every `sigma` and every lift, a padded lift of the conjugate
    representation `sigma'`. Nothing in the problem changes, and `nu^A = nu^B = +infinity` at
    every `eta`.
  - So the argument must either restrict the class of lifts or apply an infimum over lifts.
    Both are the lift-optimized escape of the target.
