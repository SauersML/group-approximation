---
rg: 2
id: fpbs-tree-product-two-point-norm-is-spherical-sum
kind: claim
title: On a Cartesian product of regular trees the l2 norm of the two-point operator equals its ground-state spherical sum
distinct_from:
  fpbs-expanding-factor-product-strict-thresholds: that is a perturbative sufficient condition for p_c < p_{2->2} on products with a strongly expanding factor; this is an exact identity, with no perturbative hypothesis, for products of trees only.
  fpbs-integrated-sensitivity-universal: that is right-continuity of the walk rate lambda(p) at p_c on every Cayley graph; this is an identity for the operator norm, i.e. for p_{2->2}, on tree products.
---

**ESTABLISHED.**

**Setting.** Fix `r >= 1` and `a_1, ..., a_r >= 3`. Let `X` be the Cartesian
product `T_{a_1} □ ... □ T_{a_r}`, with vertex set `V`. This is the Cayley
graph of `Γ = Π_i (Z/2)^{*a_i}` for the standard generators. The examples
T3xT10, F2xF6 and ZxF3 of `fpbs-pointwise-critical-growth-decay-fails` are of
this form, where `F_k` is `T_{2k}` and `Z` is `T_2`. The case `a_i = 2` is
excluded only to keep the formulas uniform. The same proof works there, with
`φ_2 ≡ 1`.

Notation:

- For `u, v in V`, the type is `t(u,v) = (d(u_1,v_1), ..., d(u_r,v_r))` in `N^r`.
- `S_t(o)` is the set of `v` with `t(o,v) = t`, and
  `|S_t| = Π_i N_{a_i}(t_i)`, where `N_a(0) = 1` and `N_a(m) = a (a-1)^{m-1}`.
- The ground-state spherical function of `T_a` is
  `φ_a(m) = (1 + m (a-2)/a) (a-1)^{-m/2}`.
- Put `Φ(t) = Π_i φ_{a_i}(t_i)`.

**Theorem.** Let `f : N^r -> [0, ∞)` and set `K_f(u,v) = f(t(u,v))`. Then

```text
||K_f||_{l2(V) -> l2(V)}  =  σ(f)  :=  Σ_t f(t) |S_t| Φ(t)   in [0, ∞].
```

**Corollary.** Let `τ_p` be the two-point function of Bernoulli bond
percolation on `X` and `T_p` its operator.

1. `||T_p||_{2->2} = Σ_t τ_p(t) |S_t| Φ(t)`.
2. `|S_t| Φ(t)` is within constant factors of `Π_i (1+t_i) (a_i - 1)^{t_i/2}`.

So

```text
p_{2->2}(X) = sup{ p : Σ_t τ_p(t) Π_i (1+t_i)(a_i-1)^{t_i/2} < ∞ },
```

and `p_c < p_{2->2}` on `X` holds exactly when this scalar series converges
for some `p > p_c`.

The corollary applies because Bernoulli percolation is invariant under
`Aut(X) ⊇ Π_i Aut(T_{a_i})`, so `τ_p(u,v)` depends only on `t(u,v)`.

## Proof

**Step 1 (sphere sums are polynomials in A).** On `T_a`, let `A_m` be the
sphere-sum operator `(A_m h)(u) = Σ_{d(u,w)=m} h(w)`. Then:

- `A_0 = I` and `A_1 = A`;
- `A A_1 = A_2 + a I`;
- `A A_m = A_{m+1} + (a-1) A_{m-1}` for `m >= 1`.

So `A_m = P_m(A)` for a real polynomial `P_m` that does not depend on the
root.

Let `h(w) = φ_a(d(o,w))`. The two-term recurrence has a double root, so
`φ_a` solves it:

- `a φ_a(1) = 2 sqrt(a-1)` at `m = 0`;
- `φ_a(m-1) + (a-1) φ_a(m+1) = 2 sqrt(a-1) φ_a(m)` for `m >= 1`.

Hence `A h = 2 sqrt(a-1) h` pointwise, and so
`A_m h = P_m(2 sqrt(a-1)) h`. Evaluating at `o` gives
`P_m(2 sqrt(a-1)) = N_a(m) φ_a(m)`. Therefore, for every `u` and `m`,

```text
Σ_{d(u,w)=m} φ_a(d(o,w))  =  N_a(m) φ_a(m) φ_a(d(o,u)).        (F)
```

Every sum here is finite, so no convergence question arises.

**Step 2 (upper bound: Schur test).** Put `H(v) = Φ(t(o,v)) > 0`. The shell
`S_t(u)` is the product of the factor spheres, so applying (F) in each factor
gives

```text
(K_f H)(u) = Σ_t f(t) Σ_{w in S_t(u)} H(w) = σ(f) H(u).
```

`K_f` is symmetric and nonnegative. For `x, y in l2(V)`:

```text
|<K_f x, y>| <= Σ K_f(u,v) (x_u^2 H(v)/H(u) + y_v^2 H(u)/H(v)) / 2
             <= σ(f) (||x||^2 + ||y||^2) / 2.
```

Scaling `x` and `y` gives `||K_f|| <= σ(f)`.

**Step 3 (lower bound: spectral corner).** Suppose first that `f` has finite
support.

- Let `A^{(i)}` be the adjacency operator along factor `i`. These are
  commuting self-adjoint operators on `l2(V) = ⊗_i l2(T_{a_i})`.
- `K_f = Q(A^{(1)}, ..., A^{(r)})`, where
  `Q(λ) = Σ_t f(t) Π_i P^{(a_i)}_{t_i}(λ_i)`.
- The joint spectrum is `Π_i [-2 sqrt(a_i-1), 2 sqrt(a_i-1)]` (Kesten, for
  each factor).
- So `||K_f|| = sup |Q|` over that box, which is at least the value of `Q` at
  the corner `λ_i = 2 sqrt(a_i - 1)`. By Step 1 that value is
  `Σ_t f(t) Π_i N_{a_i}(t_i) φ_{a_i}(t_i) = σ(f)`.

For general `f`, let `f_R = f 1_{max t_i <= R}`.

- For nonnegative kernels, `||K||` is the supremum of `<K x, y>` over
  nonnegative unit vectors, so it is monotone in the kernel.
- Hence `||K_f|| >= ||K_{f_R}|| = σ(f_R)`, and `σ(f_R) -> σ(f)` by monotone
  convergence.

Together with Step 2 this proves the Theorem.

**Step 4 (Corollary).**

- Invariance of `P_p` under `Π_i Aut(T_{a_i})` gives `τ_p(u,v) = f_p(t(u,v))`,
  and `T_p = K_{f_p}`.
- For the size of the weights,
  `N_a(m) φ_a(m) = (a/(a-1)) (1 + m(a-2)/a) (a-1)^{m/2}` for `m >= 1`.

## What it rules out

The identity makes "is `T_{p_c}` bounded on a tree product" a
convergence question for one series.

On `T_3 □ T_10`, along the diagonal type `(k,k)`:

- the weight is `|S_{(k,k)}| Φ(k,k) = Θ(k^2 · 18^{k/2})`;
- so a divergence certificate from the diagonal alone needs
  `Σ_k τ_pc(k,k) k^2 18^{k/2} = ∞`, which requires decay per diagonal step
  no faster than `18^{-1/2} ≈ 0.2357`.

What the diagonal edge-disjoint 2-path blocks give (the live-bus lemma
`fpbs-pointwise-critical-growth-decay-fails` of wave swarm-0917, which is
not in this graph snapshot):

- they give `τ_pc(k,k) >= (2 p_c^2 - p_c^4)^k`;
- `1/12 <= p_c <= p_c(T_10) = 1/9` gives per-step factors in
  `[0.0138, 0.0247]`;
- so they fall short by a factor of at least `9.5^k`.

The pointwise-failure bounds therefore give no counterexample to
`p_c < p_{2->2}` on `T_3 □ T_10`. Whether true `τ_pc` reaches the threshold
is exactly the open scalar question of the Corollary.

Independently, `p_c < p_u` is already known on every product with a tree
factor through its nonunimodular transitive subgroups
(`fpbs-hyperbolic-and-nonunimodular-nonuniqueness`).
