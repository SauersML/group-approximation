---
rg: 2
id: deligne-third-floor-failure-is-continuous-untwisting-proof
kind: route
title: Take the ultralimit of the phase profiles of a counterexample sequence, read the flat holonomy on the limit as a continuous untwisting, and push every candidate limit back to an exact finite model or into the Bernoulli-profinite obstruction
target: deligne-third-floor-failure-is-continuous-untwisting
requires: [deligne-opnorm-monomial-models-are-almost-flat-circle-bundles, deligne-multiplier-survives-on-bernoulli-times-profinite-actions]
---

Notation of the target.

**Imported, verbatim.**
- From `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles` (ESTABLISHED):
  - the defect "`eps(rho) = max_r || rho(r) e(-theta k_r) - I ||_op`", for models "`rho(s) = D_s P_s`, where the
    permutations `P_s` realize the action on `X` *exactly*, and `D_s` is diagonal";
  - (L1) "Every monomial `theta`-model satisfies `4 mu_theta(X) <= eps(rho)`, and some model attains
    `eps = |e(mu_theta(X)) - 1| <= 2 pi mu_theta(X)`", with
    "`mu_(1/q)(X) = (1/q) min { ||f_R||_cell : f in kappa + q H^2(Y_X; Z) }`";
  - (L3) "`kappa(Z_2(Y_X; Z)) = D(Lambda) Z`, where `D(Lambda)` is the order of `z` in `H_1(Lambda~; Z)` ... Moreover
    `D(Lambda)` lies in `{1, 2}` for every finite-index `Lambda`";
  - "A disjoint union takes the maximum over its orbits."
- From `deligne-multiplier-survives-on-bernoulli-times-profinite-actions` (ESTABLISHED), with its setting "α ∈
  Z^2(Γ, μ_3) is a normalized cocycle of Deligne's triple cover E_3 = μ_3 ×_α Γ ... X an ergodic profinite action
  of Γ, or a point ... B = (Y_0,ν)^Γ a Bernoulli shift with any standard base": "For β ∈ {α, α²}, no measurable
  c : Γ × Z → T satisfies c(g, hz) c(h, z) = β(g,h) c(gh, z) for a.e. z, when Z = X or Z = B × X (diagonal
  action)." Call this (DM1).

**Standard facts used** (no citation node).
- Ultralimits along a nonprincipal ultrafilter `U` on `N` exist in compact metric spaces; Tychonoff; weak*
  compactness of Borel probabilities on a compact metric space.
- A continuous map on a compact metric space is uniformly continuous; a locally constant one takes finitely many
  values and is uniformly locally constant.
- `Gamma(M)` is normal of finite index in `Gamma` and `intersection_M Gamma(M) = 1`.

## Conventions

- Write the node's `D_s P_s` model as `rho(s) e_x = e(a(x, s)) e_(s x)`, i.e. `a(x, s)` is the node's diagonal
  entry at `s x`. This is a relabeling of the phases only.
- For an inverse letter put `a(x, s^(-1)) := -a(s^(-1) x, s)`, so that `rho(s)^(-1) e_x = e(a(x, s^(-1))) e_(s^(-1) x)`.
- For a relator `r = t_1 ... t_m` (letters in `S^(+-1)`) put `w_i = t_i ... t_m` (`w_(m+1) = e`) and
  `H_r(x) = sum_i a(w_(i+1) x, t_i)`. Since `r` acts trivially on `X`, `rho(r) = diag e(H_r)`, hence

  ```text
  eps(rho) = max_(x, r) | e(H_r(x) - k_r / 3) - 1 |    (theta = 1/3).
  ```

- A cocycle `c : G x K -> T` over an action means `c(gh, y) = c(g, h y) + c(h, y)`. For a word it gives
  `c(t_1 ... t_m, y) = sum_i c(t_i, w_(i+1) y)`, with `c(s^(-1), y) = -c(s, s^(-1) y)`.
- `|e(t) - 1| = 2 |sin(pi t)|` lies between `4 dist(t, Z)` and `2 pi dist(t, Z)`.

## Step 1: no finite model is exact

Let `X` be a finite `Gamma`-set. Then `mu_(1/3)(X) > 0`.
- By the disjoint-union clause, it suffices to take `X` transitive.
- For `f in kappa + 3 H^2(Y_X; Z)` and the cycle `Sigma` of (L3) with `kappa(Sigma) = D in {1, 2}`,
  `f(Sigma) = D + 3 g(Sigma) != 0`. So `f_R != 0` and `||f_R||_cell > 0`.
- The real classes `f_R` form a coset of the image of `3 H^2(Y_X; Z)`, a discrete subgroup of the
  finite-dimensional space `H^2(Y_X; R)`. So the minimum in (L1) is attained and is positive.

Consequently no monomial `1/3`-model over a finite `Gamma`-set has `eps = 0`, because (L1) would give
`mu_(1/3)(X) = 0`. Call a model with `H_r(x) = k_r / 3` in `T` for all `x, r` **exact**; no exact model exists.

A continuous untwisting restricted to a finite invariant subset `O` of `K` is an exact model on `O`: with
`a(x, s) = c(s, x)`, the word formula gives `H_r(x) = c(r, x) = c(z^(k_r), x) = k_r / 3`. The same holds for any
cocycle `b : E_3 x O -> T` on a finite `Gamma`-set with `b(z, .) = 1/3`.

## Step 2: descent lemma

Let `K` be a compact metrizable `Gamma`-space and `c_0 : S x K -> T` continuous. Let `F' = F(S + {z})` act on `K`
through `F' -> E_3 -> Gamma`, so `z` acts trivially.
- Extend `c_0` by `c(z, y) = 1/3` to the unique cocycle `c` of `F'` on `K` given by the word formula. Each `c(w, .)` is
  continuous.
- **Lemma.** `c` descends to `E_3 = <S, z | [z, s], r z^(-k_r), z^3>` iff `c(r, y) = k_r / 3` for all `r in R`,
  `y in K`. It is then a continuous untwisting.

*Proof.* Let `N = ker(F' -> E_3)`; it acts trivially on `K`.
1. If `c(n, .) = 0` for all `n in N`, then `c(g n, y) = c(g, n y) + c(n, y) = c(g, y)`, so `c` is well defined on `E_3`.
2. The set `N_0 = {n in ker(F' -> Gamma) : c(n, .) = 0}` is a subgroup: for `n, n'` acting trivially,
   `c(n n', y) = c(n, y) + c(n', y)` and `0 = c(e, y) = c(n^(-1), n y) + c(n, y)`.
3. It is normal in `F'`: `c(u n u^(-1), y) = c(u, u^(-1) y) + c(n, u^(-1) y) + c(u^(-1), y) = c(u u^(-1), y) = 0`.
4. So it suffices to check the relators. With `z` acting trivially:
   - `c(z s z^(-1) s^(-1), y) = 1/3 + c(s, s^(-1) y) - 1/3 + c(s^(-1), y) = c(e, y) = 0`;
   - `c(r z^(-k_r), y) = c(r, y) - k_r / 3`, which is `0` iff `c(r, y) = k_r / 3`;
   - `c(z^3, y) = 1 = 0` in `T`.
5. Conversely `r = z^(k_r)` in `E_3`, so a descended cocycle has `c(r, y) = k_r / 3`. QED.

## Step 3: floor failure gives an approximable untwisted space

Assume `inf_X mu_(1/3)(X) = 0`.

**3a. Models.** By (L1) there are finite `Gamma`-sets `X_n^0` and models `a_n^0` with `eps_n -> 0`. So
`eta_n := max_(x, r) dist(H_r(x) - k_r / 3, Z) <= eps_n / 4 -> 0`. Put `X_n = X_n^0 x Gamma / Gamma(n!)` with the
diagonal action and `a_n((x, q), s) = a_n^0(x, s)`. The holonomy is pulled back, so `eta_n` is unchanged.

**3b. Profiles.** Let `P = T^(Gamma x S) x prod_(M >= 1) (Gamma / Gamma(M) + {*})`, compact metrizable. `Gamma`
acts continuously by `(h y)_(g, s) = y_(g h, s)` on the first factor and by left translation (fixing `*`) on each
`Gamma / Gamma(M) + {*}`. This is a left action: `(h_1 (h_2 y))_(g, s) = y_(g h_1 h_2, s)`. Define
`pi_n : X_n -> P` by

```text
pi_n(x, q) = ( (a_n(g (x, q), s))_(g, s) , (xi_M)_M ),   xi_M = q mod Gamma(M) if M | n!, else *.
```

It is exactly equivariant: `pi_n(h x)_(g, s) = a_n(g h x, s) = (h pi_n(x))_(g, s)`, and `q -> h q` commutes with
reduction.

**3c. The limit set.** Fix a nonprincipal ultrafilter `U`. Let `K` be the set of `y in P` such that every open
`V` containing `y` meets `pi_n(X_n)` for `U`-many `n`.
- `K` is closed: if `y notin K`, a witnessing `V` witnesses the same for all its points.
- `K` is invariant: `pi_n(X_n)` is invariant and each `h` is a homeomorphism.
- For every `delta > 0`, `{n : pi_n(X_n) is contained in N_delta(K)}` is in `U`. Otherwise pick `x_n` with
  `d(pi_n(x_n), K) >= delta` for `U`-many `n`, and let `y = lim_U pi_n(x_n)`. Every open `V` containing `y`
  contains `pi_n(x_n)` for `U`-many `n`, so `y in K`, yet `d(y, K) >= delta`. The same argument with arbitrary
  `x_n` shows `K` is nonempty.

**3d. The cocycle.** For `r = t_1 ... t_m` define a continuous `G_r : P -> T` by
`G_r(y) = sum_i gamma_i(y)`, where `gamma_i(y) = y_(w_(i+1), s)` if `t_i = s` and
`gamma_i(y) = -y_(s^(-1) w_(i+1), s)` if `t_i = s^(-1)`. On profiles,
`gamma_i(pi_n(x)) = a_n(w_(i+1) x, t_i)` by the inverse-letter convention, so `G_r(pi_n(x)) = H_r(x)`. Hence
`dist(G_r - k_r / 3, Z) <= eta_n` on `pi_n(X_n)`. For `y in K`, `y` is a limit of points of `pi_n(X_n)` along `U`,
so `G_r(y) = k_r / 3` by continuity.

Put `c_0(s, y) = y_(e, s)`. The word formula gives `c(t_i, w_(i+1) y) = gamma_i(y)`: for `t_i = s` this is
`(w_(i+1) y)_(e, s) = y_(w_(i+1), s)`, and for `t_i = s^(-1)` it is `-(s^(-1) w_(i+1) y)_(e, s)`. So
`c(r, y) = G_r(y) = k_r / 3` on `K`, and by Step 2 `c` is a continuous untwisting on `K`.

**3e. Freeness and the map to `Gamma^bar`.** For each `M`, the conditions `xi_M != *` and
"`xi_(M')` reduces to `xi_M`" (for `M | M'`) are clopen and hold on `pi_n(X_n)` for all `n >= M'`. So they hold on
`K`, and `y -> (xi_M(y))_M` is a continuous `Gamma`-map `K -> Gamma^bar`. The stabilizer in `Gamma` of any point of
`Gamma^bar` is contained in every `Gamma(M)`, hence trivial. So `Gamma` acts freely on `K`.

**3f. Approximation and measure.**
- Choose `n_1 < n_2 < ...` with `pi_(n_j)(X_(n_j))` inside `N_(1/j)(K)`, and `pi~_j(x) in K` with
  `d(pi~_j(x), pi_(n_j)(x)) <= 1/j`. With `omega_s` a modulus of continuity of `s` on `P`,
  `d(pi~_j(s x), s pi~_j(x)) <= 1/j + omega_s(1/j) -> 0`. So `K` is finitely approximable, and the `pi_n` are
  exactly equivariant into `P` at distance `-> 0` from `K` along the subsequence.
- The measures `nu_n = (pi_n)_* (uniform on X_n)` are `Gamma`-invariant. Their weak* limit `nu` along `U` is
  invariant. For each `delta`, `nu_n` is carried by the closed set `closure N_delta(K)` for `U`-many `n`, so `nu` is
  too. Hence `nu(K) = 1`.

This proves the forward direction of (U) and all the listed extra properties.

## Step 4: an approximable untwisted space gives floor failure

Let `K` carry a continuous untwisting `c` and finite approximations `pi_n : X_n -> K` with
`D_n = max_(x, s) d(pi_n(s x), s pi_n(x)) -> 0`. Put `a_n(x, s) = c(s, pi_n(x))`.

**4a. Words.** For every fixed word `w` in `S^(+-1)`, `max_x d(pi_n(w x), w pi_n(x)) -> 0`. Induct on `w = t w'`:

```text
d(pi_n(t w' x), t w' pi_n(x)) <= d(pi_n(t x'), t pi_n(x')) + omega_t( d(pi_n(w' x), w' pi_n(x)) ),   x' = w' x.
```

For `t = s` the first term is at most `D_n`. For `t = s^(-1)` put `u = s^(-1) x'`; the first term is
`d(pi_n(u), s^(-1) pi_n(s u)) <= omega_(s^(-1))(D_n)`. Here `omega_t` is a modulus of continuity on `K`.

**4b. Holonomy.** Compare `H_r(x) = sum_i a_n(w_(i+1) x, t_i)` with
`c(r, pi_n(x)) = sum_i c(t_i, w_(i+1) pi_n(x)) = k_r / 3` term by term.
- `t_i = s`: `c(s, pi_n(w_(i+1) x))` against `c(s, w_(i+1) pi_n(x))`.
- `t_i = s^(-1)`: `-c(s, pi_n(s^(-1) w_(i+1) x))` against `-c(s, s^(-1) w_(i+1) pi_n(x))`.

By 4a and uniform continuity of `c(s, .)`, every difference tends to `0` uniformly in `x`. So
`max_(x, r) dist(H_r(x) - k_r / 3, Z) -> 0`, hence `eps(rho_n) -> 0` and `mu_(1/3)(X_n) <= eps(rho_n) / 4 -> 0` by
(L1). Any orbit of `X_n` has `mu` at most this, by the disjoint-union clause, so the floor fails over transitive
sets too. This proves (U).

## Step 5: the four constraints

**(C1).** A finite orbit `O` of `K` would carry the exact model of Step 1 (restrict `c` to `O`), which does not
exist. On the free `K` of Step 3 every stabilizer is trivial; its preimage in `E_3` is `<z> = Z/3`, and
`z -> e(1/3)` is a character of it. So restricting to a stabilizer gives no contradiction.

**(C2).** Let `v : K -> T` be continuous and `c' = c + delta v`, `(delta v)(g, y) = v(g y) - v(y)`. Then `c'` is a
cocycle with `c'(z, .) = c(z, .) = 1/3`, so an untwisting. Suppose each `c'(s, .)` is locally constant.
- Then there is `eta > 0` with `c'(s, y) = c'(s, y')` whenever `d(y, y') < eta`, for all `s in S`.
- Run 4b with `c'`. By 4a, for `n` large every compared pair of points is within `eta`, for all relators. So every
  difference is exactly `0`, and `H_r(x) = c'(r, pi_n(x)) = k_r / 3`: an exact model, contradicting Step 1.
- A continuous map to a finite subgroup of `T` is locally constant.

*The example `K_3`.* Let `K_3''` be the set of `omega in (Z/3)^(E_3)` with `omega(h z) = omega(h) + 1`, with
`(g omega)(h) = omega(g^(-1) h)`.
- The condition is invariant, and `(z omega)(h) = omega(h z^(-1)) = omega(h) - 1`, since `z` is central. So `z`
  acts freely and `K_3 = K_3'' / <z>` is a compact metrizable `Gamma`-space. It is nonempty: prescribe `omega` on a
  section of `E_3 -> Gamma`.
- `c(g, [omega]) = (omega(e) - omega(g^(-1))) / 3` is well defined (both terms shift by `1`) and continuous.
- It is a cocycle: `c(g, h[omega]) + c(h, [omega])` is `(omega(h^(-1)) - omega(h^(-1) g^(-1)) + omega(e) - omega(h^(-1))) / 3`,
  which is `c(g h, [omega])`.
- `c(z, [omega]) = (omega(e) - omega(z^(-1))) / 3 = 1/3`.

Its values lie in `(1/3) Z / Z`, so by the above `K_3` is not finitely approximable. Neither is the free space
`K_3 x Gamma^bar`, with `c` pulled back.

**(C3).** Let `nu` be an invariant probability on `K`, and suppose `phi : Z -> K` is a measurable map with
`phi(h w) = h phi(w)` for a.e. `w` and all `h`, where `Z` is `X`, `B` (that is, `B x point`) or `B x X` as in (DM1).
- Write `E_3 = mu_3 x_alpha Gamma` as in (DM1), with multiplication `(a, g)(b, h) = (a b alpha(g, h), g h)`. The
  central `mu_3` is `<z>`; let `zeta_0` be the element corresponding to `z`, and write `alpha(g, h) = zeta_0^(j(g, h))`.
- With the section `sigma(g) = (1, g)`, `sigma(g) sigma(h) = z^(j(g, h)) sigma(g h)`.
- Put `d(g, w) = c(sigma(g), phi(w))`, a measurable map `Gamma x Z -> T`. The cocycle identity and `c(z^j, .) = j/3`
  give, for a.e. `w`,

  ```text
  d(g, h w) + d(h, w) = c(sigma(g) sigma(h), phi(w)) = j(g, h) / 3 + d(g h, w).
  ```

- So `C = e(d)` satisfies `C(g, h w) C(h, w) = beta(g, h) C(g h, w)` with `beta = chi o alpha`, where
  `chi(zeta_0^j) = e(j/3)` is an injective character of `mu_3`. Hence `beta in {alpha, alpha^2}`, contradicting
  (DM1).

**(C4).** Take the data of the target.
- Every relator word `w_(i+1)`, and `s^(-1) w_(i+1)`, has length at most `L`. So each term `a_n(w_(i+1) x, t_i)` is a
  continuous function of `(xi_n(k x))_(k in B_(R + L))` and of `q_n(w_(i+1) x) = w_(i+1) q_n(x)`.
- Hence `H_r(x) = D_r(p_n(x), q_n(x))` for continuous functions `D_r : A^(B_(R+L)) x Gamma/Gamma(M) -> T`, which
  do not depend on `n`.

Suppose `liminf eps(rho_n) = 0`, i.e. along a subsequence `max_x dist(H_r(x) - k_r/3, Z) -> 0`.
- Hausdorff density persists along the subsequence. So every `(p, q)` is a limit of realized pairs, and by
  continuity `D_r(p, q) = k_r / 3` for every `(p, q)` and every `r`.
- Fix `a_* in A`. The finite `Gamma`-set `Gamma / Gamma(M)` with constant label `a_*` and phases
  `a(q, s) = F_s(const a_*, q)` has holonomy `D_r(const a_*, q) = k_r / 3`. That is an exact model, contradicting
  Step 1.

*Random labels.* Let the labels be i.i.d. with a law `lambda` of full support on `A`. Fix `delta` and a finite
cover of `A^(B_(R+L))` by `N` open sets, each of `lambda^(B_(R+L))`-measure at least `p > 0`.
- At `m` centres `x` of class `q` with pairwise disjoint injective balls `B_(R+L) x`, the patterns are independent
  with law `lambda^(B_(R+L))`.
- The probability that some cover set is missed is at most `N (1 - p)^m`.
- So if `m -> infinity` for each of the finitely many `q`, the density hypothesis holds with probability tending to 1.

## Step 6: the connected example

Let `K''` be the set of `omega in T^(E_3)` with `omega(h z) = omega(h) + 1/3`, with `(g omega)(h) = omega(g^(-1) h)`.
- As for `K_3`, `z` acts by `omega -> omega - 1/3`, freely, and `K = K'' / <z>` is a compact metrizable
  `Gamma`-space.
- `c(g, [omega]) = omega(e) - omega(g^(-1))` is a continuous untwisting, by the computation for `K_3` with `1/3` in
  place of `1`.
- Fix a section `sigma : Gamma -> E_3`. Every `h` is uniquely `sigma(g) z^j`, and `omega -> (omega(sigma(g)))_g` is a
  homeomorphism `K'' -> T^Gamma`. So `K''` is connected, and so is `K`.

**No untwisting of `K` is locally constant on `S x K`.** Let `c'` be any continuous untwisting of `K` with each
`c'(s, .)` locally constant. `K` is connected, so each `c'(s, .)` is constant. By the word formula each
`c'(g, .)` is constant, and the cocycle identity makes `chi(g) = c'(g, .)` a homomorphism `E_3 -> T` with
`chi(z) = 1/3`. On the one-point `Gamma`-set, `a(pt, s) = chi(s)` is an exact model, contradicting Step 1.
(Equivalently, `chi` lifts to `Gamma~`, factors through `H_1(Gamma~; Z)`, and `D(Gamma) chi(z) = 0` with
`D(Gamma) in {1, 2}` by (L3).) In particular no untwisting of `K` is continuously cohomologous to a locally constant
one.

**The free space `K x Gamma^bar`.** It is free because `Gamma^bar` is, and `c` pulls back to it. Let `c'` be an
untwisting of it with each `c'(s, .)` locally constant.
- Each fibre `K x {xi}` is connected, so `c'(s, (y, xi)) = b(s, xi)` for a locally constant `b(s, .)` on `Gamma^bar`.
- A locally constant function on the profinite space `Gamma^bar` factors through some `Gamma / Gamma(M)`.
- So `b` defines phases on the finite `Gamma`-set `Gamma / Gamma(M)`, and the word formula at any point `(y, xi)`
  gives holonomy `c'(r, (y, xi)) = k_r / 3`. That is an exact model, contradicting Step 1.

Neither space is claimed to be finitely approximable or not; that is exactly the open (NFA).
