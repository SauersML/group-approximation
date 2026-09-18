---
rg: 2
id: wold-multiplicity-commutant-packing-proof
kind: route
title: Average conjugated shift packings into the commutant and bound the averaging operator by its Hilbert--Schmidt trace
target: wold-multiplicity-blinds-commutant-packing-sizes
requires: []
---

Notation as in the target. Every map `Ad U` with `U` unitary preserves `||.||_op`, `||.||_2`
and the inner product `tr(a^* b)`. For unitaries `a, b` and an operator `x`,

```text
||[a,x]||_2 - ||[b,x]||_2 <= 2 ||a-b||_2 ||x||_op.
```

## Lemma 0: transporting microstates

Put `beta_n = max_s ||sigma_n(u) sigma_n(s) sigma_n(u)^-1 - sigma_n(w_s)||_2`. Then
`lim_omega beta_n = 0`, because `sigma` is a homomorphism of `G` and `u s u^-1 = w_s`.

For `x in X_n(eps)`, conjugate by `sigma_n(u)`:

```text
||[sigma_n(s), T_n x]||_2 = ||[sigma_n(u) sigma_n(s) sigma_n(u)^-1, x]||_2
                         <= ||[sigma_n(w_s), x]||_2 + 2 R beta_n
                         <= L eps + 2 R beta_n.
```

The last step telescopes along the word `w_s`. So `T_n X_n(eps) ⊆ X_n(L eps + 2 R beta_n)`. By
induction:

```text
T_n^j X_n(eps) ⊆ X_n(c_j),    c_j <= L^j (eps + 2 R j beta_n).        (0)
```

`X_n(eps)` and `D_n(theta)` are convex and symmetric, because all their defining conditions are
seminorm bounds.

## WH1

Fix `delta`, `K` and `eps > 0`. Choose `theta_1 > 0` with

```text
L^K (1 + 2RK) theta_1^2 <= min(eps, theta_1),     8 K^2 theta_1^(1/2) <= delta^2 / 2.   (1)
```

Every smaller `theta_1` also satisfies (1). For `omega`-almost every `n`, `beta_n <= theta_1^2`.
Fix such an `n`, and let `p_1, ..., p_P` be a maximal `delta`-separated subset of
`D_n(theta_1)`. For `i in [P]^K` put

```text
z_i = K^-1 sum_(k=0)^(K-1) T_n^k p_(i_k).
```

**Membership.** By (0) and (1), `T_n^k p_(i_k) in X_n(c_k(theta_1^2)) ⊆ X_n(eps)` for `k < K`.
By convexity, `z_i in X_n(eps)`.

**Separation.** Take `i != i'` and put `a_k = p_(i_k) - p_(i'_k)`. Then

```text
K^2 ||z_i - z_i'||_2^2 = sum_k ||a_k||_2^2 + sum_(k != l) tr((T^k a_k)^* T^l a_l).
```

- The first sum is at least `delta^2`, since some `a_k` has `||a_k||_2 >= delta`.
- Take `k < l`. The inner product is `tr(a_k^* T^(l-k) a_l)`. Write `a_k = 2a'` and `a_l = 2b`,
  with `a' in D_n(theta_1)` and `b in X_n(theta_1^2)`, using convexity and symmetry. Then
  `T^(l-k) a_l = 2T(w)` with `w = T^(l-k-1) b`, and `w in X_n(c_(l-k-1)(theta_1^2)) ⊆ X_n(theta_1)`
  by (0) and (1).
- The defining test of `D_n(theta_1)` gives `|tr(a_k^* T^(l-k) a_l)| = 4|tr(a'^* T w)| <= 4 theta_1^(1/2)`.
  The terms with `k > l` are complex conjugates of these.
- So the cross sum is at most `4 K^2 theta_1^(1/2) <= delta^2/2`.

Hence `||z_i - z_i'||_2 >= delta / (sqrt 2 K)`, and

```text
P_(delta/(sqrt 2 K))(X_n(eps)) >= P_delta(D_n(theta_1))^K    for omega-a.e. n.
```

Take logarithms, divide by `f(d_n)`, and take `lim_omega`.
- The left side does not depend on `theta_1`. The right side holds for all small `theta_1`, so it
  dominates `K liminf_(theta->0) lim_omega (...) = K h_D^f(delta)`.
- Taking the infimum over `eps` gives WH1.

**Consequence.** Let `t <= delta_0/sqrt 2` and `K = floor(delta_0/(sqrt 2 t)) >= 1`. Then
`delta_0/(sqrt 2 K) >= t`, and `h_A^f` is nonincreasing in its argument. So

```text
h_A^f(t) >= h_A^f(delta_0/(sqrt 2 K)) >= K c >= c delta_0/(2 sqrt 2 t).
```

## WH2

Take a finite symmetric `F ⊆ Gamma` and pick a word `v_gamma` for each `gamma in F`. Let `W` be
the set of words `{v_gamma, v_gamma^-1 : gamma in F}`. Then:
- `W = W^-1`;
- `N = |W| >= |F|`;
- each fibre of `W -> Gamma` has at most 2 elements;
- `L_W` denotes the maximal word length in `W`.

Define `Phi = N^-1 sum_(w in W) Ad sigma_n(w)` on `(M_(d_n), tr(a^* b))`.
- `sigma_n` is a free-group homomorphism, so `Ad sigma_n(w^-1) = (Ad sigma_n(w))^*`. Hence
  `Phi` is selfadjoint with `||Phi|| <= 1`.
- `Ad U`, as an operator on `M_d`, has trace `|Tr U|^2`. So

```text
d^-2 Tr(Phi^2) = N^-2 sum_(w,w' in W) |tr sigma_n(w w')|^2
  -> N^-2 #{(w,w') : w w' = 1 in Gamma} <= 2/N      (along omega).
```

This uses `tr sigma_n(v) -> tau(sigma(v))`, which is `1` if `v = 1` in `Gamma` and `0` otherwise.
Put `m_n = d^-2 Tr(Phi^2)`.

Let `E` be the spectral projection of `Phi` for `|lambda| >= 1/2`. Since `Tr Phi^2 >= rank(E)/4`,
the complex rank `r` of `E` is at most `4 m_n d^2`.

Take `x in X_n(eps)`.
- Telescoping gives `||Ad sigma_n(w) x - x||_2 <= |w| eps`. So `||(1-Phi) x||_2 <= L_W eps`.
- On the range of `1-E`, `|1-lambda| >= 1/2`. Since `E` commutes with `Phi`,
  `||(1-E)x||_2 <= 2||(1-Phi)x||_2 <= 2 L_W eps`.
- `E x` lies in the radius-`R` ball of a real Euclidean space of dimension `2r`. That ball has a
  `delta`-net of size `(1 + 2R/delta)^(2r) <= (3R/delta)^(8 m_n d^2)` for `delta <= R`.

If `2 L_W eps <= delta`, the net is a `2 delta`-net for `X_n(eps)`, so

```text
log P_(4 delta)(X_n(eps)) <= 8 m_n d_n^2 log(3R/delta).
```

- Taking `limsup_omega` gives the displayed quantitative bound.
- Since `Gamma` is infinite, `N` can be taken arbitrarily large. So `h_A^(d^2)(4 delta) = 0` for
  `delta <= R`, and `h_A^(d^2)` vanishes identically by monotonicity.
- `h_B^(d^2) = h_A^(d^2)` by WH3.
- `D_n(theta) ⊆ X_n(theta^2)` gives `h_D <= h_A`.

## WH3

`X^B_n(eps) = T_n^-1 X_n(eps)`, and `T_n^-1` is a `||.||_2`-isometry. So packing numbers agree
at every radius.

## WH4

Let `(Gamma, S)` have Kazhdan constant `kappa`. Then `Gamma' = u^-1 Gamma u` with generators
`S' = u^-1 S u` has the same constant.

**Averaging lemma.** Let `nu` be uniform on `S' cup {1}` and `pi = Ad sigma` on `L^2(M^omega)`.
- For `eta` orthogonal to the `pi(Gamma')`-fixed vectors,
  `<(1 - pi(nu)) eta, eta> = (2(|S|+1))^-1 sum_(s' in S') ||pi(s') eta - eta||^2 >= kappa^2 ||eta||^2 / (2(|S|+1))`.
- The spectrum of `pi(nu)` lies in `[-1 + 2/(|S|+1), 1]`. So `pi(nu)^m` converges in operator
  norm to the projection `P` onto the fixed vectors.
- For `x in M^omega` with `||x||_op <= R`, each `pi(nu)^m x` lies in the operator-norm `R`-ball.
  That ball is `||.||_2`-closed in `L^2(M^omega)` (recalled standard fact for finite von Neumann
  algebras).
- So `Px in M^omega` is bounded and `Ad sigma(Gamma')`-fixed, hence
  `Px in A_1 = sigma(u)^* A sigma(u)`.

**Rounding.** The Kazhdan inequality applied to `(1-P)xi` gives
`||xi - P xi||_2 <= max_(s') ||pi(s') xi - xi||_2 / kappa`.

**Proof of WH4.** Fix `theta < kappa^2/R^2`.
- `||[sigma_n(s), y_n]||_2 -> 0` along `omega`, so the commutator condition holds
  `omega`-almost surely.
- Suppose that for an `omega`-large set of `n` some `w_n in X_n(theta)` has
  `|tr(y_n^* T_n w_n)| > theta^(1/2)`. Put `w_n = 0` elsewhere and `w = [w_n]`.
- Then `xi = T w = sigma(u)^* w sigma(u)` is bounded by `R`, with
  `||[sigma(s'), xi]||_2 <= theta` for `s' in S'`.
- So `||xi - P xi||_2 <= theta/kappa`, and `P xi in A_1`.
- Since `y ⊥ L^2(A_1)`, `|tau(y^* xi)| = |tau(y^*(xi - P xi))| <= R theta/kappa`.
- But `tau(y^* xi) = lim_omega tr(y_n^* T_n w_n)` has modulus at least `theta^(1/2)`. This
  forces `theta >= kappa^2/R^2`, a contradiction.
