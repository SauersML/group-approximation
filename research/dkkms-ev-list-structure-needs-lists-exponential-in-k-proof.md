---
rg: 2
id: dkkms-ev-list-structure-needs-lists-exponential-in-k-proof
kind: route
title: Restrict to defect edges whose new direction leaves phi^(-1)(phi(L')), where both branches agree and the direction is uniform off a proper subspace, bound agreement of any non-matching reference by one half, count matching references by the injectivity of d -> y_d on X_U, and compare with the 2^-k outer soundness floor
target: dkkms-ev-list-structure-needs-lists-exponential-in-k
requires:
  - dkkms-list-seed-needs-lists-exponential-in-l
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
artifacts:
  - experiments/ugc-ev-list-2026-09-17/check_ev_list_kernel_rank.py
---

The notation is that of the target. "LS" is Theorem LS of
`dkkms-list-seed-needs-lists-exponential-in-l`, and "LS Step j" and "LS Lemma j"
refer to its route `dkkms-list-seed-needs-lists-exponential-in-l-proof`. "The
decoding node" is `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`.
The results used are these.

* **Decoding node, annotation and item 3.** Each copy `e` of an output
  `((U,L),(V,L'))` has direction `x_e ∈ L \ L'`, and given `((V,L'), U)` the
  direction is uniform on `X_U \ (L' + H_U)`. Also `L = L' + <x_e>`.
* **Decoding node, item 4.** `K = 1`. **Outer game:** `pi_UV(alpha) = alpha|_V`
  if `alpha` satisfies all equations of `U`, and `⊥` otherwise.
* **LS Lemma 1.** Given `V`, `L'` is uniform on the `(l-1)`-spaces of `X_V`
  avoiding `H'`.
* **LS Lemma 3 and Step 2.** When `x` satisfies every equation, the unfolding
  of `h` at `(U,L)` is `a|_L`, where `a` is the branch assignment of `c(L)`.
  The value and the satisfied mass on `G_multi` equal the folded ones.
* **LS (4.1), Lemmas 5 and 6, Lemma 7.** These give
  `N = dim(M̄ ∩ N0) + dim c(L')`, the law of `N` within `2^(l-k)` of `N_l`,
  `Pr[M̄ ∩ N0 != 0 | V] <= 2^(-s-1)` and `Pr[p ∈ P | V] < 2^(-s-1)` for
  `p != 0`.
* **LS Steps 6 and 7.** These give `beta_bad <= delta_sur/(1 - 2^(l-1-k))`,
  J-instances of every rank `n` with `delta_sur < 2^(n-k)`, `x = 0`
  satisfying everything, and `val(h) >= v(l) - 2^(l-k) - beta_bad`.

## Step 1: Lemma A

Put `S = X \ W`. Then `|ker psi ∩ S| = |ker psi| - |ker psi ∩ W|`. Since
`ker psi ∩ W` is `W` (if `W <= ker psi`) or a hyperplane of `W`, it has size
`>= |W|/2`, with equality iff `W` is not inside `ker psi`. So
`|ker psi ∩ S| <= |X|/2 - |W|/2 = |S|/2`. ∎

## Step 2: the defect edges

Fix a tuple `U` and a smoothed `V` on which `Phi` is onto `X_V`, hence onto
`X_U`. Fix `L'` with `L' ∩ H' = 0`. Put `P_phi := phi(L')` and
`W_U := X_U ∩ phi^(-1)(P_phi)`. Since `phi` kills `H_U`,
`L' + H_U <= W_U`. Since `dim P_phi <= l-1 < l`, `W_U` is a proper subspace of
`X_U`.

Call a copy `e` with this `(U, V, L')` a **defect edge** if `c(L') = <(0,d)>`
is one-dimensional and `phi(x_e) ∉ P_phi`.

**Lemma B.** On a defect edge:
(a) `c(L) = c(L')`, so the A-label unfolds to `y_d|_L` and the B-label is
`y_d|_(L')`, and the edge is satisfied with `ev_e(h) = y_d(x_e)`;
(b) conditional on `(U, V, L')` and on the edge being a defect edge, `x_e` is
uniform on `X_U \ W_U`.

*Proof.* (a) `Phi(L) = Phi(L') + <Phi(x_e)>`. An element of `Phi(L)` outside
`Phi(L')` is `Phi(u) + Phi(x_e)` with `u ∈ L'`. It lies in `K` only if
`phi(x_e) = phi(u) ∈ P_phi`, which is excluded. So `c(L) = c(L')`, and by LS
Lemma 3 the A-label unfolds to `y_d|_L`. The B-label is `y_d|_(L')` by
definition of `h`, so the edge is satisfied, and `ev_e` is the unfolding
evaluated at `x_e`. (b) By item 3, `x_e` is uniform on `X_U \ (L' + H_U)`.
The defect condition is `x_e ∉ W_U`, and `L' + H_U <= W_U`, so the
conditional law is uniform on `X_U \ W_U`. ∎

**Lemma C (mass of defect edges).** For surjective `V`,

```text
Pr[defect edge | V]  >=  (3/4)(Pr[N = 1 | V] - 2^(-s-1)).
```

*Proof.* By LS (4.1), `N = 1` and `M̄ ∩ N0 = 0` give `dim c(L') = 1`. By
LS Lemma 7(a) the second condition fails with probability `<= 2^(-s-1)`.
Given `L'` with nullity `N`, `|W_U| = 2^(3k - l + (l-1-N))`. By item 3,
`Pr[x_e ∉ W_U | L'] = (2^(3k) - |W_U|)/(2^(3k) - 2^(l-1+k))`, which is at least
`1 - 2^(-1-N)`. This equals `3/4` at `N = 1`. ∎

## Step 3: what a t-list covers on defect edges

Fix a t-list `(lambda^j_U)` and an index map `i(U,V,L')`. On a defect edge,
the edge is ev-covered iff `psi(x_e) = 0`, where
`psi := lambda^(i(U,V,L'))_U - y_d|_(X_U)`. Here `psi` is a functional on
`X_U` that is fixed given `(U,V,L')`.

* If `psi != 0`, Lemma A with `W = W_U` and Lemma B(b) give a conditional
  covering probability `<= 1/2`.
* If `psi = 0`, then `y_d|_(X_U)` belongs to `T_U := {lambda^1_U, ..., lambda^t_U}`.

The map `d -> y_d|_(X_U)` is injective on `F_2^s`, because
`y_d - y_(d') = <d + d', zeta(·)>` and `zeta` is onto on `X_U`. So the set
`D_U := {d != 0 : y_d|_(X_U) ∈ T_U}` has at most `t` elements. For each
`d ∈ D_U`, LS Lemma 7(b) gives
`Pr[c(L') = <(0,d)> | V] <= Pr[(0,d) ∈ P | V] < 2^(-s-1)` for every
surjective `V`.

Let `mu_def` be the `G_multi` mass of defect edges. Summing over
`(U, V, L')` with the edge weights:

```text
covered defect mass  <=  (1/2) mu_def  +  (1/2) sum_(U,V) mu(U,V) sum_(d ∈ D_U) Pr[c(L') = <(0,d)> | V]
                     <   (1/2) mu_def  +  t 2^(-s-2).
```

Every defect edge is satisfied by Lemma B(a). So

```text
D(h, Lambda)  >=  mu_def - covered  >  (1/2) mu_def - t 2^(-s-2).        (3.1)
```

The index map may depend on the whole of `(U, V, L')`. It may not depend on
`x_e`, and in List-Str_t it depends on `(V, L')` only.

## Step 4: Theorem EL

By Lemma C, LS Lemma 5 (`Pr[N = 1 | V] >= P(N_l = 1) - 2^(l-k)`, since
`d' >= k`) and the mass `beta_bad` of non-surjective tuples:

```text
mu_def  >=  (1 - beta_bad)(3/4)(P(N_l = 1) - 2^(l-k) - 2^(-s-1))
        >=  (3/4) P(N_l = 1) - (3/4)(2^(l-k) + 2^(-s-1) + beta_bad).
```

With (3.1), this gives the bound on `D` in Theorem EL. The value bound is
LS Step 6 verbatim. ∎

## Step 5: Corollary EL, item 1

Take the J-instance of LS Step 7 with `n = k - 8`, so `s = k - l - 8`, and
`x = 0`. Then:
* `delta_sur < 2^(-8)` and `beta_bad <= 2^(-8)/(1 - 2^(l-1-k))`;
* `s >= 2` because `k >= 3l >= 24`;
* for `t < 2^(s-3)`, `t 2^(-s-2) < 1/32`.

At `k = 3l` the artifact (Part C) evaluates, exactly as rationals and for
every `8 <= l <= 64`,

```text
v(l) - 2^(l-k) - beta_bad                                        >= 0.605,
(3/8) P(N_l = 1) - 1/32 - (3/8)(2^(l-k) + 2^(-s-1) + beta_bad)    >  0.110.
```

At `l = 8` the second quantity is `0.11037`. Every error term decreases as `k`
grows at fixed `l`. For `l > 64`, LS Lemma 6 gives `TV(N_l, N_64) < 2^(-64)`,
and the error terms only shrink. So for every `l >= 8` and `k >= 3l`:
* `val(h) >= 0.605 >= 1/2 + gamma` for every `gamma <= 0.105`;
* `D(h, Lambda) > 0.110 > gamma >= gamma - gamma'` for every t-list with
  `t < 2^(k-l-11)`.

The outer labellings of List-Str_t are special t-lists. Their index map
depends on `(V,L')` only, and their functionals are assignments `lambda_U`
with `<lambda_U, x_e> = lambda_U(x_e)`. So (List-Str_t(gamma, gamma', eps))
fails on this YES input, for every `gamma'` and `eps`. The J-instance is a
perfectly satisfiable regular 3LIN instance (LS Step 7), hence a YES input of
regular Gap3Lin (DKKMS Theorem 4.1) for every completeness parameter. ∎

## Step 6: Corollary EL, items 2 and 3

**Floor.** The tuples in `U` consist of pairwise variable-disjoint equations
(decoding node, verbatim). For uniform `a ∈ F_2^X` the `k` equations of `U`
are then independent fair events, so `a` satisfies all of them with
probability exactly `2^(-k)`. Under the honest outer labelling `lambda^a`, the
pair `(U,V)` is consistent iff `a` satisfies `U`, because then
`pi_UV(a|_U) = a|_V = lambda^a_V`. So
`E_a val(lambda^a) = 2^(-k)`, and some `a` has `val(Phi_k) >= 2^(-k)`. This
holds on every instance, NO instances included.

**(S) with loss `t^(-alpha)`.** Suppose
`2^(-k) <= s_out < (p^2/(t^alpha K^2) - 2 eps)/2`, with `K = 1`,
`p = gamma'^3 2^(-l-2)` and `alpha >= 1`. Then
`t^alpha < p^2 2^(k-1) = gamma'^6 2^(k-2l-5)`.
* For `alpha = 2`, which is (S_t), this gives `t < gamma'^3 2^(k/2-l-5/2)`.
* For general `alpha >= 1` and `t >= 1`, it gives `t < max(1, 2^(k-2l-5))`.

**Dichotomy.** We have `k/2 - l - 5/2 < k - l - 11` iff `k > 17`, and
`k - 2l - 5 < k - l - 11` iff `l > 6`. Also `1 < 2^(k-l-11)` because
`k >= 3l >= 24`. So any `t` allowed by (S) has `t < 2^(k-l-11)`, and then
item 1 refutes List-Str_t. ∎

## What the artifact checks

`check_ev_list_kernel_rank.py` runs in about 15 seconds and exits 0 iff all
checks pass.
* **Part A.** Lemma A, including the equality case, for every proper subspace
  and every nonzero functional of `F_2^m`, `m <= 5`.
* **Part B.** Step 3 exactly in the image model `X_U = Q = F_2^(n+1)`,
  `H_U = 0`, `Phi` the first `n` coordinates. It takes `(l,s) = (3,2)` and
  `(4,1)`, all `L' ∈ Gr(Q, l-1)` and all `x_e ∉ L'`. The lists are all lists of
  one or two functionals and all lists of branch assignments with `t <= 4`, with
  the best index per `L'`. Each list has
  `D >= mu_def/2 - (1/2) sum_(d ∈ D_U) Pr[c(L') = <(0,d)>] >= mu_def/2 - t 2^(-s-2)`.
  It also checks `max_d Pr[c(L') = <(0,d)>] < 2^(-s-1)`.
* **Part C.** The numbers of Step 5 for every `8 <= l <= 64` at `k = 3l`, and
  the exponent comparisons of Step 6.
