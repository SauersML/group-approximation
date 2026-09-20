---
rg: 2
id: virtually-abelian-higman-tuples-collapse-opnorm-proof
kind: route
title: Cocycle averaging makes finite-image tuples dense in virtually abelian tuples, and finite-image collapse passes to the closure
target: virtually-abelian-higman-tuples-collapse-opnorm
requires: [finite-image-higman-models-collapse-opnorm, one-small-higman-generator-collapses-the-four-cycle]
artifacts:
  - experiments/virtually-abelian-higman-2026-09-17/check_va_collapse.py
  - experiments/virtually-abelian-higman-2026-09-17/out_check_va_collapse.txt
---

Notation as in the target.  All norms are operator norms, and indices `i`
run over `Z/4`.  `D`, `M`, `VA_k`, `FIN_k` and `dist` are as defined there.

## Imported input

From `finite-image-higman-models-collapse-opnorm` (ESTABLISHED), verbatim:

> **Theorem (FIC).**  Let `u = (u_x)_(x in X)` be unitaries in `U(k)`, for
> any `k`, such that the group `Gamma = <u_x>` is **finite**.  Put
> `delta = max_r ||r(u) - 1||_op`.  If `delta < 1/2`, then
> `max_x ||u_x - 1||_op <= C_G delta.`

and, for `Hig = <g_0..g_3 | g_i g_(i+1) g_i^(-1) g_(i+1)^(-2)>`,
"`C_Hig = 1`".  For the relator `r_i = g_i g_(i+1) g_i^(-1) g_(i+1)^(-2)`,
right multiplication by the unitary `u_(i+1)^2` gives

```text
||r_i(u) - 1|| = || u_i u_(i+1) u_i^* - u_(i+1)^2 ||,
```

so the `delta` of (FIC) is our `D(u)`.  Hence

```text
(FIC-Hig)   u in FIN_k and D(u) < 1/2   ==>   M(u) <= D(u).
```

From `one-small-higman-generator-collapses-the-four-cycle` (ESTABLISHED),
verbatim: "every generator in any nontrivial homomorphism from Higman's
group into the unitary group of a matrix norm corona has distance at least
`2 sin(2 pi/5)` from the identity."  This is used only for the numerical
value `1/10` in (VA4).

Standard Lie-theoretic facts used:

- (L1) Cartan's closed-subgroup theorem: a closed subgroup `K <= U(k)` is a
  compact Lie group, and its identity component `K^0` is an open normal
  subgroup of finite index.
- (L2) A compact connected abelian Lie group `T` is a torus.  Its
  exponential map `exp : Lie(T) = R^r -> T` is a surjective continuous
  homomorphism with kernel a lattice.  Hence `T` is divisible, and
  `T[m] = {t : t^m = 1}` is finite, of order `m^r`.  Moreover
  `sup_{t in T} dist(t, T[L]) -> 0` as `L -> infinity`.  For the last point,
  lift `t` into a compact fundamental domain.  The lattice `(1/L) Z^r` is
  `1/L`-dense there in the sup norm, and `exp` is uniformly continuous on
  compact sets.

## Step 0: two perturbation estimates

Let `u, v` be in `U(k)^4` with `max_i ||u_i - v_i|| <= eta`.

(P1) `D(v) <= D(u) + 5 eta`.  In `u_i u_(i+1) u_i^* - u_(i+1)^2`, the letter
`u_i` occurs twice and `u_(i+1)` three times.  Replacing one unitary letter
of a product of unitaries changes the product by at most the norm of that
letter's change.  So each relator difference changes by at most `5 eta`.

(P2) `|M(u) - M(v)| <= eta`, since `| ||u_i - 1|| - ||v_i - 1|| | <= ||u_i - v_i||`.

## Step 1: the two descriptions of `VA_k` agree

Let `Gamma = <u_0,..,u_3> <= U(k)`, and let `K` be its closure.

- Suppose `A <= Gamma` is abelian of finite index, and write
  `Gamma = union_(j<=J) gamma_j A`.
  - The closure of `A` is an abelian closed subgroup.
  - `K = union_j gamma_j closure(A)`, because the closure of a finite union
    is the union of the closures.
  - So `closure(A)` has finite index in `K`, and is therefore open and
    closed.
  - Hence `K^0 <= closure(A)`, and `K^0` is abelian.
- Conversely, suppose `K^0` is abelian.  Then `Gamma cap K^0` is abelian, and
  its index in `Gamma` is at most `|K/K^0|`, which is finite by (L1).

If `u` lies in some closed `K'` with `(K')^0` abelian, then
`K <= K'`, so `K^0 <= (K')^0` is abelian.  Thus `u in VA_k` if and only
if `u` lies in some closed subgroup of `U(k)` with abelian identity
component.  By (L2) such an identity component is a torus `T`.

## Step 2: (VA1), finite subgroups exhaust a torus extension

Let `K <= U(k)` be closed, with `T = K^0` a torus.  Put `Q = K/T`, a finite
group, and `N = |Q|`.

**Action.**  For `x in Q` and any `kappa in K` in the coset `x`, the map
`t -> kappa t kappa^(-1)` is an automorphism of `T` (as `T` is normal).  It
depends only on `x`, because `T` is abelian.  Write it `t -> x.t`.  It
preserves each finite subgroup `T[m]`.

**Cocycle.**  Choose a set-theoretic section `s : Q -> K` of `K -> Q`, with
`s(1) = 1`, and put

```text
f(x,y) = s(x) s(y) s(xy)^(-1)   in T.
```

Expanding `s(x) s(y) s(z)` in the two possible ways, and using
`s(x) t = (x.t) s(x)` for `t in T`, gives the cocycle identity:

```text
f(x,y) f(xy,z) = (x.f(y,z)) f(x,yz)      for all x,y,z in Q.   (C1)
```

In detail:

- `(s(x)s(y))s(z) = f(x,y) s(xy) s(z) = f(x,y) f(xy,z) s(xyz)`;
- `s(x)(s(y)s(z)) = s(x) f(y,z) s(yz) = (x.f(y,z)) f(x,yz) s(xyz)`.

**Averaging.**  Put `F(x) = prod_(z in Q) f(x,z)` in `T`.  Take the product
of (C1) over `z in Q`.  `T` is abelian, `x.` is a homomorphism, and `yz`
runs over `Q` as `z` does.  So

```text
f(x,y)^N F(xy) = (x.F(y)) F(x).                                   (C2)
```

By divisibility (L2), choose `g(x) in T` with `g(x)^N = F(x)`, and put
`s'(x) = g(x)^(-1) s(x)`.  This is again a section.  Its cocycle is

```text
f'(x,y) = s'(x) s'(y) s'(xy)^(-1)
        = g(x)^(-1) (x.g(y))^(-1) f(x,y) g(xy).
```

Here conjugation by `g(x) in T` acts trivially on `T`, so `s'(x)` induces
the same automorphism `x.` as `s(x)`.  Raising to the power `N` and using
(C2):

```text
f'(x,y)^N = F(x)^(-1) (x.F(y))^(-1) f(x,y)^N F(xy) = 1.
```

So `f'` takes values in the finite group `T[N]`.

**Finite subgroups.**  For every multiple `m` of `N` put

```text
F_m = { t s'(x) : t in T[m], x in Q }.
```

This is a finite set, of size `m^r N`.  It is closed under multiplication:

```text
t s'(x) t' s'(y) = t (x.t') s'(x) s'(y) = [ t (x.t') f'(x,y) ] s'(xy).
```

The bracket lies in `T[m]`, because `x.t'` is in `T[m]` and `f'(x,y)` is in
`T[N] <= T[m]`.  A finite subset of a group that is closed under
multiplication is a subgroup.  So `F_m <= K` is a finite subgroup.
Moreover `F_m <= F_(m')` whenever `m` divides `m'`.

**Density.**  Every `kappa in K` can be written `kappa = t s'(x)`, with
`x = kappa T` and `t = kappa s'(x)^(-1)` in `T`.  Take `m_L = N L!`.  Then
`T[m_L]` contains `T[L]`, so `dist(t, T[m_L]) -> 0` uniformly in `t` by (L2).
Hence the increasing union of the `F_(m_L)` is dense in `K`.

**Tuples.**  Let `u` be in `VA_k`, with `K` the closure of `<u>` as in
Step 1.  Given `eta > 0`, choose `L` so large that every `t` in `T` is within
`eta` of `T[m_L]`.  Write `u_i = t_i s'(x_i)`, choose `t_i'` in `T[m_L]` with
`||t_i - t_i'|| <= eta`, and put `v_i = t_i' s'(x_i)`.  Then:

- all `v_i` lie in the finite group `F_(m_L)`, so `v` is in `FIN_k`;
- `||u_i - v_i|| = ||(t_i - t_i') s'(x_i)|| = ||t_i - t_i'|| <= eta`.

This proves (VA1).

## Step 3: (VA2)

Let `u` be in `VA_k` with `D(u) < 1/2`.  By (VA1) choose `v^(m)` in
`FIN_k` with `eta_m = max_i ||u_i - v^(m)_i|| -> 0`.  By (P1),
`D(v^(m)) <= D(u) + 5 eta_m < 1/2` for all large `m`.  So (FIC-Hig) and
(P2) give

```text
M(u) <= M(v^(m)) + eta_m <= D(v^(m)) + eta_m <= D(u) + 6 eta_m.
```

Letting `m -> infinity` gives `M(u) <= D(u)`.

Sharpness: let `z` be a unimodular scalar, and put `u_j = z` and `u_i = 1`
for `i != j`.  The relator at `i = j-1` equals `z - z^2`, of norm `|z - 1|`.
The relator at `i = j` equals `z z^* - 1 = 0`.  The other two vanish.  So
`D(u) = |z - 1| = M(u)`, and `u` generates a cyclic, hence abelian, group.

## Step 4: (VA3)

Since `FIN_k <= VA_k <= closure(FIN_k)` by (VA1), and a distance to a set
equals the distance to its closure, we have `dist(u, VA_k) = dist(u, FIN_k)`.

Let `v` be in `VA_k` with `eta = max_i ||u_i - v_i||`.  By (P1),
`D(v) <= D(u) + 5 eta`.  There are two cases.

- If `D(u) + 5 eta >= 1/2`, then `eta >= (1/2 - D(u))/5`.
- Otherwise `D(v) < 1/2`.  Then (VA2) and (P2) give

  ```text
  M(u) <= M(v) + eta <= D(v) + eta <= D(u) + 6 eta,
  ```

  so `eta >= (M(u) - D(u))/6`.

In both cases `eta >= min((1/2 - D(u))/5, (M(u) - D(u))/6)`.  Taking the
infimum over `v` gives (VA3).

## Step 5: (VA4)

Let `Q = prod_n M_(k_n) / (+)_n M_(k_n)`, where `(+)_n` is the `c_0` direct
sum.  So the norm of the class of `(x_n)` is `limsup_n ||x_n||`.

**Distance.**  Let `u^(n)` be unitary lifts of `rho(g_0),..,rho(g_3)`.

- `rho` is a homomorphism, so each relator is `1` in `Q`.  This means
  `limsup_n ||r_i(u^(n)) - 1|| = 0` for each `i`, so `D(u^(n)) -> 0`.  (The
  hypothesis `D(u^(n)) -> 0` in (VA4) is therefore automatic for any lifts.)
- `M_rho = max_j limsup_n ||u^(n)_j - 1|| = limsup_n M(u^(n))`, because a
  maximum of finitely many limsups is the limsup of the maximum.
- Choose a subsequence `n_l` with `M(u^(n_l)) -> M_rho`.  Along it, (VA3)
  gives

  ```text
  dist(u^(n_l), VA_(k_(n_l))) >= min((1/2 - D(u^(n_l)))/5, (M(u^(n_l)) - D(u^(n_l)))/6)
                              -> min(1/10, M_rho/6).
  ```

  So `limsup_n dist(u^(n), VA_(k_n)) >= min(1/10, M_rho/6)`.
- Since `rho` is nontrivial and the `g_j` generate `Hig`, some `rho(g_j)`
  is `!= 1`.  The imported fact then gives `M_rho >= 2 sin(2 pi/5) > 1.9`.
  Hence `M_rho/6 > 0.31 > 1/10`, and the minimum is `1/10`.

**Homomorphisms into products of virtually abelian groups.**  Let
`K_n <= U(k_n)` be closed with abelian identity component, and put
`G = prod_n K_n / {(x_n) : ||x_n - 1|| -> 0}`.

- The map `prod_n K_n -> U(Q)` has kernel exactly `{(x_n) : ||x_n - 1|| -> 0}`,
  because `x - 1` lies in `(+)_n M_(k_n)` exactly when `||x_n - 1|| -> 0`.
  So `G` is a subgroup of `U(Q)`.
- Let `rho : Hig -> G` be a homomorphism, and choose lifts `u^(n)` in
  `K_n^4`.  As above, `D(u^(n)) -> 0`.  By Step 1 each `u^(n)` lies in
  `VA_(k_n)`.
- For all large `n` we have `D(u^(n)) < 1/2`, so (VA2) gives
  `M(u^(n)) <= D(u^(n)) -> 0`.
- Hence `rho(g_j) = 1` for every `j`, and `rho` is trivial.

For a free ultrafilter `omega`, replace `->` by `->_omega` throughout.  Then
`{n : D(u^(n)) < 1/2}` lies in `omega`.  On that set `M(u^(n)) <= D(u^(n))`,
so `M(u^(n)) ->_omega 0`, and again `rho` is trivial.

## Step 6: (VA5)

By (VA3), `dist(u, VA_k) = dist(u, FIN_k)`.  So the `VA_k` version of (FA)
is literally the same statement as (FA), and it suffices to treat `FIN_k`.

**(HMF5) implies (FA).**  Given `eta > 0`, let `delta'` be the `delta` of
(HMF5) for `epsilon = eta`, and put `delta = delta'/2`.

- If `D(u) <= delta`, then `D(u) < delta'`, so `M(u) < eta`.
- The trivial tuple `(1,1,1,1)` lies in `FIN_k`, and its distance from `u`
  is exactly `M(u)`.
- So `dist(u, FIN_k) <= M(u) < eta`.

**(FA) implies (HMF5).**  Given `epsilon > 0`, put
`c = min(1/20, epsilon/12)` and `eta = c/2`.  Let `delta_0` be the `delta`
of (FA) for this `eta`, and put `delta = min(delta_0, 1/4, epsilon/2)`.

Let `u` be in `U(k)^4` with `D(u) < delta`, and suppose, for a
contradiction, that `M(u) >= epsilon`.

- `(1/2 - D(u))/5 > (1/2 - 1/4)/5 = 1/20`.
- `(M(u) - D(u))/6 > (epsilon - epsilon/2)/6 = epsilon/12`.
- So (VA3) gives `dist(u, FIN_k) > c`.
- But `D(u) < delta <= delta_0`, so (FA) gives `dist(u, FIN_k) <= eta = c/2`.

This is a contradiction, so `M(u) < epsilon`.  Here `delta` does not depend
on `k`, so this is (HMF5).

## Status

Every step uses only the two imported ESTABLISHED nodes, quoted verbatim
above, and the standard facts (L1) and (L2).  Hence the target is
ESTABLISHED.  The script and its output are numerical sanity checks and are
not load-bearing.
