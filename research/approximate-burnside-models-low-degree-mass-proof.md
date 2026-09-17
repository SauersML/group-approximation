---
rg: 2
id: approximate-burnside-models-low-degree-mass-proof
kind: route
title: The weak-* limit of the small pieces lives on the Burnside representation variety, kills a finite-index subgroup, and positive-definiteness caps its mass
target: approximate-burnside-models-low-degree-trace-mass-vanishes
requires:
  - bounded-degree-partial-burnside-reps-factor-through-burnside
---

**Proof.** Notation as in the claim. `tr` and `||.||_2` are normalized, and
`||xy||_2 <= ||x||_op ||y||_2`, `||xy||_2 <= ||x||_2 ||y||_op`.

**Step 0: `K_c` has finite index.** Let `rho : F -> U(d)`, `d <= c`, satisfy
`rho(g)^N = 1` for all `g in F`. Then `rho in X_R(d)` for every `R`, so by
clause 2 of `bounded-degree-partial-burnside-reps-factor-through-burnside`,
`rho(F)` is finite of order `<= M_c := max_(d <= c) f(d) N^d`. So `ker rho` is a
normal subgroup of `F` of index `<= M_c`. The free group `F` of rank `m` has only
finitely many subgroups of index `<= M_c` (each is the stabilizer of a point in
one of the finitely many actions of `F` on `{1, ..., M_c}`). Hence `K_c`, the
intersection of all such kernels, is a finite intersection of finite-index
subgroups, and `C(m,N,c) = [F : K_c] < infinity`. Moreover

```text
tr rho(w) = 1   for every such rho and every w in K_c.          (0)
```

**Step 1: split the trace.** Fix `c` and write `P_k = P_k^(c)`, `alpha_k =
alpha_k(c)`. If `limsup alpha_k = 0` there is nothing to prove. Otherwise
pass to a subsequence along which `alpha_k -> alpha' = limsup alpha_k > 0`; we
show `alpha' <= C(m,N,c)/|G|`. `P_k` commutes with
every `w(u^(k))`, so for `x` in the group algebra `C[F]`

```text
tr x(u^(k)) = alpha_k tr_s^(k)(x) + tr((I - P_k) x(u^(k))),            (1)
tr_s^(k)(x) = tr(P_k x(u^(k))) / alpha_k,
```

and the last term of (1) is `>= 0` when `x = y* y`, since it is the trace of a
positive operator. For every word `w`, `P_k` reduces `v = w(u^(k))`, so

```text
alpha_k tr_s^(k)(|w^N - 1|^2) <= || w(u^(k))^N - I ||_2^2 =: eps_k(w) -> 0.   (2)
```

**Step 2: the small part as a measure.** By the structure of finite-dimensional
`C*`-algebras, `P_k C^(d_k)` is an orthogonal sum of irreducible
subrepresentations `pi_(k,1), pi_(k,2), ...` of `F`, each of dimension `<= c`.
Choosing orthonormal bases, each `pi_(k,i)` is a point of the compact metrizable
space

```text
Y_c = disjoint union over d <= c of U(d)^m,
```

and `tr_s^(k)(w) = integral of tr rho(w) d nu_k(rho)`, where `nu_k` is the
probability measure giving `pi_(k,i)` the weight `dim pi_(k,i) / (alpha_k d_k)`
and `tr` on `U(d)` is normalized. For a word `w` the function
`f_w(rho) = tr |rho(w)^N - 1|^2` is continuous and nonnegative on `Y_c`, and
(2) reads `integral f_w d nu_k <= eps_k(w) / alpha_k -> 0`. Pass to a further
subsequence with `nu_k -> nu` weak-*. Then `integral f_w d nu = 0` for every
word `w`, so `f_w = 0` on `supp nu` for each of the countably many `w`. So every
`rho in supp nu` satisfies `rho(w)^N = 1` for all `w in F`: `supp nu` lies in the
union of the `Hom(B(m,N), U(d))`, `d <= c`.

**Step 3: the limit kills `K_c`.** `rho -> tr rho(w)` is continuous on `Y_c`, so
`tr_s^(k)(w) -> sigma(w) := integral tr rho(w) d nu`. By (0), `sigma(w) = 1` for
every `w in K_c`.

**Step 4: positive-definiteness.** Let `H` be the image of `K_c` in `G = F/L`,
so `[G : H] <= C(m,N,c)` and `|H| >= |G| / C(m,N,c)` (with `H` infinite when
`G` is infinite). Take any finite `s <= |H|` and `s` distinct
elements of `H` with lifts `w_1, ..., w_s in K_c`, and `x = w_1 + ... + w_s`.
Then `x* x = sum_(i,j) w_i^(-1) w_j` with every `w_i^(-1) w_j in K_c`, and
`w_i^(-1) w_j in L` exactly when `i = j`. Take the limit of (1) along the
subsequence:

```text
s = tau(x* x) >= lim alpha_k tr_s^(k)(x* x) = alpha' sigma(x* x) = alpha' s^2.
```

So `alpha' <= 1/s` for every `s <= |H|`, hence `alpha' <= 1/|H| <= C(m,N,c)/|G|`,
and `alpha' = 0` if `G` is infinite. This proves clause 1. ∎

**Clause 2.** Put `b_i = E_k(u_i^(k))`. `E_k` is a compression by a partition
of unity into projections, so `||b_i||_op <= 1` and
`||u_i - b_i||_2 <= delta_k` (dropping `k`). Then

```text
|| b_i* b_i - I ||_2 = || b_i*(b_i - u_i) + (b_i - u_i)* u_i ||_2 <= 2 delta_k.
```

`b_i` is block-diagonal for `C^(d_k) = V_(k,1) + ... + V_(k,r_k) + W_k`. Take a
polar decomposition `b_i = v_i |b_i|` block by block, with `v_i` unitary and
block-diagonal. Since `|t - 1| <= |t^2 - 1|` for `t >= 0`,
`||b_i - v_i||_2 = || |b_i| - I ||_2 <= || b_i* b_i - I ||_2 <= 2 delta_k`, so
`||u_i - v_i||_2 <= 3 delta_k`. For a word `w` of length `|w|`, telescoping and
unitary invariance give `||w(u) - w(v)||_2 <= 3 |w| delta_k`, hence
`||w(v)^N - w(u)^N||_2 <= 3 N |w| delta_k`. So `v^(k)` is an approximate
exponent-N model with the same limit trace `tau`. Each `V_(k,j)` is invariant
under `v^(k)`, so its irreducible pieces have dimension `<= c`, and the
low-degree mass of `v^(k)` is `>= beta_k`. Clause 1 applied to `v^(k)` gives
`limsup beta_k <= C(m,N,c)/|G|`. ∎

**Remark (scope).** Steps 1 to 3 use only the approximate law. Step 4 uses that
`tau` is a regular trace; for a general limit trace the same steps give the
decomposition `tau = alpha' sigma + (1 - alpha') sigma'`, with `sigma` a
positive-definite function constant on the cosets of the finite-index subgroup
`K_c` and `sigma'` positive-definite. So the low-degree part of any
approximate exponent-N model has a limit trace factoring through the finite
quotient `F/K_c`, and statement 2 of
`hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness` is open only for
the high-degree part.
