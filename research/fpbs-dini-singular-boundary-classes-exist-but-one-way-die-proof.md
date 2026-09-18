---
rg: 2
id: fpbs-dini-singular-boundary-classes-exist-but-one-way-die-proof
kind: route
title: A Schottky block code with block lengths 4^n gives an ergodic Dini-singular class by the Kolmogorov 0-1 law, and a counting bound on elements whose shadow and inverse shadow both meet a one-way set makes every such class shadow-summable
target: fpbs-dini-singular-boundary-classes-exist-but-one-way-die
requires:
  - fpbs-dini-boundary-class-diagonal-dissipative
---

Full written proof. Notation is as in `fpbs-dini-boundary-class-diagonal-dissipative` and its proof: the Gromov
product `(.|.)_o`, the thin shadows `O_s(g)`, the visual metric `d_eps` with constant `C_0`, and the inputs (I1)--(I4).
Put `|g| = d(o, g o)`, `beta(R) = #{g : |g| <= R}`, and let `v` satisfy `beta(R) <= C_Gamma e^{vR}`. For `K` contained in
`dGamma`, put `Gamma_s(K) = {g : O_s(g) meets K}`. Since `O_s(g)` increases with `s`, so does `Gamma_s(K)`.

## Imported inputs

- **(S) Schottky pairs.** Let `a, b` be loxodromic with `{a^+, a^-}` and `{b^+, b^-}` disjoint. There is `N` such
  that the following holds for `A = a^N` and `B = b^N`, with `tau = max(|a|, |b|)`. The *letter path* of a positive word
  `W` in `A, B` (finite or infinite) passes through the points `W_t o`, where `W_t` is the prefix of `W` of length `t`
  in the letters `a, b`, joined by geodesic segments of length at most `tau`. Every such letter path is a
  `(lam, c)`-quasi-geodesic, with `lam, c` independent of `W`. Distinct infinite positive words give distinct endpoints.
  This is the standard ping-pong and local-to-global argument (Gromov, *Hyperbolic groups*, §5.3 and §8.5; see also
  Ghys--de la Harpe, Ch. 5 and 8). By the Morse lemma, there is `H` such that each such letter path is within Hausdorff
  distance `H` of a geodesic with the same endpoints.
- **(Ol) Ol'shanskii**, *On residualing homomorphisms and G-subgroups of hyperbolic groups*, IJAC 3 (1993), Lemma 3.8.
  A nonelementary hyperbolic `Gamma` has infinitely many loxodromic elements `g`, pairwise non-commensurable (no
  nonzero powers conjugate), with `E(g) = <g> x E(Gamma)`. Here `E(g)` is the stabilizer of `{g^+, g^-}` and `E(Gamma)`
  is the maximal finite normal subgroup. This is used only in Proposition 3.2.
- **(Lévy) Martingale convergence.** For a Borel set `F` in `2^N` and a Borel probability measure `m`,
  `m(F ∩ [x|n]) / m[x|n] -> 1` for `m`-a.e. `x` in `F`, where `[x|n]` is the cylinder of the first `n` coordinates.
- **(Kol) Kolmogorov 0-1 law.** A Borel subset of `2^N` that is invariant under changing finitely many coordinates
  has measure `0` or `1` for every product measure.

## Lemma 0: moving shadows

For `x, h, h'` in `Gamma` and `s >= 0`:
- **(a)** `x^{-1} O_s(h)` is contained in `O_{s + 2|x|}(x^{-1} h)`;
- **(b)** if `|h^{-1} h'| <= t`, then `O_s(h)` is contained in `O_{s + 2t}(h')`.

*Proof.*
- (a) Take `zeta` in `O_s(h)`. By invariance, `(x^{-1}h | x^{-1}zeta)_{x^{-1}o} = (h|zeta)_o >= |h| - s - 2 delta`.
  Moving the base point to `o` costs at most `|x|` (I1), and `|x^{-1}h| <= |h| + |x|`. So
  `(x^{-1}h | x^{-1}zeta)_o >= |x^{-1}h| - s - 2|x| - 2 delta`.
- (b) The product `(p|zeta)_o` is 1-Lipschitz in the vertex `p`, and `d(ho, h'o) = |h^{-1}h'| <= t`. So
  `(h'|zeta)_o >= |h| - s - 2 delta - t >= |h'| - s - 2t - 2 delta`.

## Theorem 1: construction of Dini-singular classes

**Step 1 (the code).** Fix a Schottky pair `A = a^N`, `B = b^N` as in (S). For Theorem 1 any loxodromic `a, b` with
disjoint fixed-point pairs will do; they exist because `Gamma` is nonelementary. Fix `n_0 >= 0` and put
`L_n = 4^{n + n_0}`. For `x` in `2^N`:
- put `A_n(0) = A^{L_n}` and `A_n(1) = B^{L_n}`;
- put `u_n(x) = A_1(x_1) A_2(x_2) ... A_n(x_n)`, a positive word of letter length `ell_n = N (L_1 + ... + L_n)`;
- let `f(x)` be the endpoint of the infinite letter path of `A_1(x_1) A_2(x_2) ...`.

By (S), `f` is well defined and injective. It is continuous, by Step 2. So `K = f(2^N)` is a Cantor set.

**Step 2 (cylinders are small).** There are `kappa > 0` and `C_1` such that, if `x` and `y` agree in their first
`n` coordinates, then `d_eps(f(x), f(y)) <= r_n = C_1 e^{-kappa ell_n}`.

*Proof.*
- The two letter paths share the initial segment up to `u_n(x) o`. Each lies within `H` of the geodesic ray from `o`
  to its endpoint, so both rays pass within `H` of `u_n(x) o`.
- Hence `(f(x)|f(y))_o >= |u_n(x)| - 2H - 4 delta`.
- By (S), `|u_n(x)| >= ell_n / lam - c`. Now apply (I2), with `kappa = eps / lam`.

**Step 3 (the measure).** Let `m` be the fair-coin product measure on `2^N`. Choose weights `c_g > 0` with
`sum_g c_g = 1`, and put `nu = sum_g c_g g_*(f_* m)`.
- *Quasi-invariance.* For `h` in `Gamma`, `h_* nu = sum_g c_{h^{-1} g} g_* f_* m`. All coefficients are positive, so
  `h_* nu` and `nu` have the same null sets.
- *Nonatomic.* `f` is injective and `m` has no atoms, so each `g_* f_* m` has no atoms.
- *Carried by `Gamma K`.* This is clear.

**Step 4 (ergodicity).** Let `E` be a `Gamma`-invariant Borel set. Suppose `x` and `y` agree beyond coordinate `n`.
Write `v_M = A_{n+1}(x_{n+1}) ... A_M(x_M)`, which is the same for `x` and `y`. Then
- `f(x) = lim_M u_n(x) v_M o`, and
- `f(y) = lim_M u_n(y) v_M o`.

Left multiplication is continuous on `Gamma ∪ dGamma`, so `f(x) = u_n(x) u_n(y)^{-1} f(y)`. Thus `f(x)` and `f(y)`
lie in one orbit, and `f^{-1}(E)` is invariant under finite coordinate changes. By (Kol), `m(f^{-1}E)` is `0` or `1`.
Then `nu(E) = sum_g c_g m(f^{-1}(g^{-1}E)) = m(f^{-1}E)` is `0` or `1`.

Only this easy direction is used: we never need points of `K` in one orbit to have tail-equivalent codes.

**Step 5 (singular to every Dini measure).** Let `lambda` be a finite Dini measure. Suppose `nu` is not singular to
`lambda`.
- *Bounded density piece.* By the Lebesgue decomposition there are `k` and a Borel set `E` with `nu(E) > 0` and
  `nu|_E <= k lambda`.
- *Moving into `K`.* Some `g` has `m(f^{-1}(g^{-1}E)) > 0`. Put `E' = g^{-1}E` and `lambda' = (g^{-1})_* lambda`.
  Then `((g^{-1})_* nu)|_{E'} <= k lambda'` and `(g^{-1})_* nu >= c_g f_* m`. So `(f_*m)|_{E'} <= (k / c_g) lambda'`.
- *`lambda'` is Dini.* `g^{-1}` is bi-Lipschitz for `d_eps` with some constant `Lip` (as in the previous proof,
  Step 5), so `omega_{lambda'}(r) <= omega_lambda(Lip r)`. Hence `lambda'` is Dini.
- *Density point.* Put `F = f^{-1}(E')`, so `m(F) > 0`. By (Lévy), choose `x` in `F` and `n_1` such that
  `m(F ∩ [x|n]) >= 2^{-n-1}` for all `n >= n_1`.
- *Lower bound on balls.* By Step 2, `f(F ∩ [x|n])` lies in `E' ∩ B(f(x), r_n)`. Hence
  `lambda'(B(f(x), r_n)) >= (c_g / k) m(F ∩ [x|n]) >= (c_g / 2k) 2^{-n}`. So
  `omega_{lambda'}(r_n) >= c' 2^{-n}` for `n >= n_1`, where `c' = c_g / 2k`.
- *Divergence.* For `r` in `[r_n, r_{n-1}]`, `omega(r) >= omega(r_n)`, and `int_{r_n}^{r_{n-1}} dr/r =
  kappa N L_n`. So `int_0^{r_{n_1}} omega_{lambda'}(r) dr/r >= sum_{n > n_1} c' 2^{-n} kappa N 4^{n + n_0} = infinity`.

This contradicts the Dini property. So `nu` is singular to every finite Dini measure, which proves Theorem 1.

*Remark (what is essential).* Divergence needs `sum_n 2^{-n} L_n = infinity`. Any `L_n` growing faster than `2^n`
works. With `L_n` bounded, the class has positive dimension and is Dini. The code has lower local dimension `0`
because cylinder masses `2^{-n}` shrink much more slowly than cylinder radii `exp(-kappa ell_n)`.

## Theorem 2: one-way supports are shadow-summable

Let `K` be compact and one-way. Put `rhobar(t) = sup_{t' <= t} rho_K(t')`, which is finite and nondecreasing (since
`Gamma_s(K)` increases with `s`, `rho_K` is already nondecreasing). Let `C` be a quasi-invariant class carried by
`Gamma K`.

**Step 1 (a standard form for the class).** Fix a finite measure `nu_0` in `C` and put `lambda = nu_0|_K`. For
weights `c_x > 0` with `sum_x c_x < infinity`, put `nu = sum_x c_x x_* lambda`. Then `nu` is in `C`.
- `nu << nu_0`, because `x_* lambda << x_* nu_0`, which is equivalent to `nu_0`.
- `nu_0 << nu`. Let `D` be contained in `xK` with `nu(D) = 0`. Then `lambda(x^{-1}D) = 0`, and `x^{-1}D` lies in `K`, so
  `nu_0(x^{-1}D) = 0`. By quasi-invariance `nu_0(D) = 0`. Since `nu_0` is carried by the countable union of the sets
  `xK`, this gives `nu_0 << nu`.

**Step 2 (counting pairs of shadows).** Put
`T_s(x, y) = #{h : O_s(h) meets xK and O_s(h^{-1}) meets yK}`.

**Lemma 1.** `T_s(x, y) <= beta(rhobar(s + 2|x| + 2|y|))`.

*Proof.* Let `h` be counted, and put `k = x^{-1}h` and `sigma = s + 2|x| + 2|y|`.
- By Lemma 0(a) applied with `x`, `O_{s+2|x|}(k)` meets `K`. So `k` is in `Gamma_sigma(K)`.
- By Lemma 0(a) applied with `y`, `O_{s+2|y|}(y^{-1}h^{-1})` meets `K`.
- Now `y^{-1}h^{-1} = (y^{-1}k^{-1}) x^{-1}`, and `|(y^{-1}k^{-1}x^{-1})^{-1} (y^{-1}k^{-1})| = |x|`. By Lemma 0(b),
  `O_sigma(y^{-1}k^{-1})` meets `K`.

So `k` is in `Gamma_sigma(K)` and `y' k^{-1}` is in `Gamma_sigma(K)` for `y' = y^{-1}`, with `|y'| <= sigma`. By
definition `|k| <= rho_K(sigma)`. Since `h = xk`, the number of such `h` is at most `beta(rho_K(sigma))`.

**Step 3 (summation).** For every `h`,

`nu(O_s(h)) nu(O_s(h^{-1})) = sum_{x,y} c_x c_y lambda(x^{-1}O_s(h)) lambda(y^{-1}O_s(h^{-1}))`
`<= lambda(K)^2 sum_{x,y} c_x c_y 1[O_s(h) meets xK] 1[O_s(h^{-1}) meets yK]`.

Summing over `h` and using Lemma 1,

`S_s(nu) <= lambda(K)^2 sum_{x,y} c_x c_y beta(rhobar(s + 2|x| + 2|y|))`.

Choose `c_x = theta_{|x|}`, where `theta_n = 2^{-n} e^{-2vn} / beta(rhobar(5n))`. This is nonincreasing,
`theta_n <= 2^{-n} e^{-2vn}`, and `sum_x c_x <= sum_n C_Gamma e^{vn} theta_n < infinity`.

Fix `s`. The pairs with `max(|x|,|y|) < s` are finitely many, and each contributes a finite amount. Now take a pair
with `M = max(|x|,|y|) >= s`.
- Then `s + 2|x| + 2|y| <= 5M`, so its term is at most `theta_M theta_0 beta(rhobar(5M)) <= 2^{-M} e^{-2vM}`.
- There are at most `2 beta(M)^2 <= 2 C_Gamma^2 e^{2vM}` such pairs.

So the tail is at most `sum_M 2 C_Gamma^2 2^{-M} < infinity`. Hence `S_s(nu) < infinity` for every `s`. The choice
of weights does not depend on `s`.

**Step 4 (no PDR).** Let `(Z, mu)` be an ergodic imp action with equivariant `xi : Z -> dGamma`, and suppose
`xi_*(mu|_B) << nu` for every `B` of finite measure. Repeat the domination step of the previous proof (Step 4,
"Domination") with `nu` in place of the Dini measure `lambda`. This gives a countable directed cover by sets
`B` with `xi_*(mu|_B) <= K_B nu`. Then `S_s(xi_*(mu|_B)) <= K_B^2 S_s(nu) < infinity`, so each `nu_B` is
shadow-summable. Theorem A of the previous claim makes the crossing diagonal totally dissipative and excludes PDR.

For a BB certificate, `fpbs-hyperbolic-bb-criterion-obstruction` item 4 gives `xi` with `xi_*(mu|_B)` in the
boundary class. So no certificate has its boundary class in `C`. This proves Theorem 2.

*Remark 1 (no size, no cocycle).* Nothing about `lambda` was used except finiteness. The weights `c_x` absorb all
translates. The only input is the combinatorial finiteness of `rho_K`: an element whose shadow meets `K` and whose
inverse, after a bounded left translation, also has a shadow meeting `K` must be short.

## Proposition 3.1: the free group

Let `Gamma = F_2 = <a, b>` with its free generators and Cayley tree (`delta = 0`). For a vertex `h` and a ray `zeta`,
`(h|zeta)_o` is the length of their common prefix. So `O_s(h)` is the set of rays that begin with the first
`ceil(|h| - s)` letters of `h`. Let `Lambda_+` be the set of rays using only the letters `a, b`, and let `K` be a
compact subset of it.

Suppose `h` is in `Gamma_s(K)`, `|y| <= s`, and `y h^{-1}` is in `Gamma_s(K)`.
- Write `h = P E`, where `P` is the positive word formed by the first `ceil(|h| - s)` letters and `|E| <= s`.
- Then `y h^{-1} = (y E^{-1}) P^{-1}`, and `|y E^{-1}| <= 2s`. Free reduction cancels at most `2s` letters of `P^{-1}`.
  So the reduced word of `y h^{-1}` ends with a terminal segment `Q` of `P^{-1}`, of length at least `|P| - 2s`, all of
  whose letters are `a^{-1}` or `b^{-1}`.
- All but the last `s` letters of `y h^{-1}` are positive, because `y h^{-1}` is in `Gamma_s(K)`. So `|Q| <= s`.

Hence `|P| <= 3s`, and `|h| <= |P| + s + 1 <= 4s + 1`. So `rho_K(s) <= 4s + 1`. The script
`experiments/dini-singular-one-way-2026-09-17/one_way_f2.py` checks this by exhaustive enumeration of reduced words of
length at most 11 for `s <= 3`, and finds `rho(s) = 2s` for `Lambda_+` itself.

With `A = a`, `B = b` and `N = 1`, the construction of Theorem 1 takes values in `Lambda_+`. So for `F_2` the
Dini-singular classes of Theorem 1 are one-way, and Theorem 2 kills them. The free-group case uses no imported input
except (Lévy) and (Kol).

## Proposition 3.2: a general hyperbolic group

**Choice of the pair.** By (Ol), choose non-commensurable loxodromic `a, b` with `E(a) = <a> x E(Gamma)` and
`E(b) = <b> x E(Gamma)`.
- *`E(Gamma)` fixes `dGamma` pointwise.* For `z` in `E(Gamma)` and loxodromic `g`, `z g^+ = lim g^n (g^{-n} z g^n) o`.
  The elements `g^{-n} z g^n` lie in the finite set `E(Gamma)`, so the limit is `g^+`. Loxodromic fixed points are
  dense in `dGamma`, and `z` acts continuously.
- *(O1) No reversal.* There are no `u` in `Gamma` and `m, n > 0` with `u a^m u^{-1} = a^{-n}`. Such a `u` would swap
  `a^+` and `a^-`, so it would lie in `E(a)`. But every element of `<a> x E(Gamma)` fixes `a^+`.
  The same holds for `b`.
- *(O2) No mixing.* There are no `u` and nonzero `m, n` with `u a^m u^{-1} = b^n`, by non-commensurability.
- The fixed-point pairs of `a` and `b` are disjoint, by (O2). Fix `A = a^N`, `B = b^N` as in (S).

**Lemma 2 (bounded oriented fellow travel).** Let `g` be `a` or `b`, and `g'` be `a^{-1}` or `b^{-1}`. Let
`D >= 0` and `m_0 >= 1`. Suppose `p, q` are in `Gamma`, `M >= 0`, and `j_0, ..., j_M` are integers such that
- `d(p g^i o, q g'^{j_i} o) <= D` for `0 <= i <= M`, and
- `j_{i'} > j_i` whenever `i' - i >= m_0`.

Then `M < m_0 (beta(D) + 1)`.

*Proof.* Put `c_i = g'^{-j_i} q^{-1} p g^i`, so `|c_i| = d(q g'^{j_i} o, p g^i o) <= D`. If `M >= m_0 (beta(D) + 1)`, the
indices `0, m_0, 2 m_0, ..., beta(D) m_0` give `beta(D) + 1` elements of the ball of radius `D`. So two coincide, say
`c_i = c_{i'}` with `i' - i >= m_0`. From `q^{-1} p = g'^{j_i} c_i g^{-i}` and the same identity at `i'`, we get
`c_i g^{i'-i} c_i^{-1} = g'^{j_{i'} - j_i}`, with `i' - i > 0` and `j_{i'} - j_i > 0`.
- If `g' = g^{-1}`, this contradicts (O1).
- Otherwise it contradicts (O2).

**Proof of Proposition 3.2.** Let `K = f(2^N)`, built from `A, B` with `L_n = 4^{n+n_0}`, and `n_0` fixed below. Let
`k` be in `Gamma_sigma(K)` and `y k^{-1}` in `Gamma_sigma(K)` with `|y| <= sigma`. We show `|k| <= A_1 sigma + A_2`.

*Step 1 (two coded paths near one geodesic).*
- *Near the codes.* Choose `zeta` in `K ∩ O_sigma(k)`. By the tripod estimate, `k o` is within `2 sigma + 8 delta`
  of the point at distance `|k|` on a geodesic ray from `o` to `zeta`. By (S) that ray is within `H` of the letter path
  of `zeta`. So some prefix `P` of the code of `zeta`, in letters, has `|k^{-1} P| <= sigma_1 = 2 sigma + 8 delta +
  H + tau`. Likewise, some prefix `Q` of the code of a point `zeta'` in `K` has `|(y k^{-1})^{-1} Q| <= sigma_1`.
- *The first path.* Let `pi_1` be the letter path of `Q`, from `o` to `Q o`. It runs from `o` to within `sigma_1` of
  `y k^{-1} o`.
- *The second path.* Let `pi_2` be the image under `y k^{-1}` of the letter path of `P`, traversed backwards. It runs
  from `y k^{-1} P o` to `y k^{-1} o`. Now `d(o, y k^{-1} P o) = |y k^{-1} P| <= |y| + |k^{-1}P| <= sigma + sigma_1`.
  In its `a`-blocks it passes through points `q (a^{-1})^j o` with `j` increasing along `pi_2`, and similarly in its
  `b`-blocks.
- *Fellow travel.* Let `gamma` be the geodesic from `o` to `y k^{-1} o`. Both `pi_1` and `pi_2` are
  `(lam, c)`-quasi-geodesics whose endpoints lie within `sigma + sigma_1` of the endpoints of `gamma`. By the Morse
  lemma and thinness of quadrilaterals, the parts of `pi_1` and `pi_2` whose projections to `gamma` lie at distance at
  least `sigma + sigma_1 + E_0` from both ends of `gamma` are within `2H + 4 delta` of `gamma` and of each other. Every vertex of one of these parts is
  therefore within `D = 2H + 4 delta + tau` of a vertex of the other.
  Here `E_0` depends only on `delta, lam, c`. This central stretch has length at least
  `|y k^{-1}| - 2(sigma + sigma_1 + E_0) >= |k| - 3 sigma - 2 sigma_1 - 2 E_0`.

*Step 2 (orientation).* Parametrize both paths by their projection to `gamma`. Projections of `(lam, c)`-quasi-geodesics
to a geodesic within distance `D` are coarsely monotone, with error `E_1 = E_1(delta, lam, c, D)`. Two points of
`pi_1` that are `m` steps apart inside one block project to points at least `m |g|_st / lam - E_1` apart, where
`|g|_st > 0` is the stable length. So for `m >= m_0(D) = ceil(lam (3 E_1 + 2D) / min(|a|_st, |b|_st)) + 1`, the
matching points on `pi_2` also appear in increasing order along `pi_2`. This is the second hypothesis of Lemma 2, with this
`m_0 = m_0(D)`. Put `ell_*(D) = m_0(D) (beta(D) + 1)`.

*Step 3 (one block on each side).* Every block of either path has letter length at least `N L_1 = N 4^{1+n_0}`, so its
projection to `gamma` has length at least `N 4^{1+n_0} / lam - E_1`. Choose `n_0` so that this is at least
`4 tau ell_*(D) + 4 E_1 + 4D`. A central stretch of length `3 (tau ell_*(D) + E_1 + D)` then contains at most two block
junctions of each path. So it contains a sub-stretch of length at least `tau ell_*(D)` lying inside a single block of
`pi_1` and a single block of `pi_2`. There the hypotheses of Lemma 2 hold with `M >= ell_*(D)`. This is impossible.

*Conclusion.* The central stretch has length less than `3 (tau ell_*(D) + E_1 + D)`. Hence
`|k| <= 3 sigma + 2 sigma_1 + 2 E_0 + 3 (tau ell_*(D) + E_1 + D)`, which is linear in `sigma`. So `K` is one-way,
with `rho_K(sigma) <= A_1 sigma + A_2`. The constants `D`, `ell_*(D)` and `m_0(D)` do not depend on `sigma`; only the
discarded end pieces do.

## Corollary and the frontier

Combine Theorem 1 (with the pair of Proposition 3.2, or the free generators for `F_2`) with Theorem 2. For every
nonelementary hyperbolic group, the resulting classes are nonatomic, ergodic, quasi-invariant and singular to every
Dini measure. They still contain a shadow-summable measure, so they cannot be the boundary class of a PDR action with a
boundary map, let alone of a Bevilacqua--Bowen certificate.

A certificate therefore needs a nonatomic ergodic class `C` that is:
- **small:** no measure dominating `C` is shadow-summable (in particular `C` is Dini-singular), and
- **two-way:** `C` is not carried by `Gamma K` for any one-way compact `K`.

*Remark 2 (what "two-way" demands).* A two-way class must satisfy the following for every compact `K` whose orbit carries it: for some
`s` there are arbitrarily long `h` whose shadow meets `K` while a bounded left translate of `h^{-1}`
also has a shadow meeting `K`. In coding terms, long subwords of typical points must reappear *reversed and inverted*,
up to a bounded conjugator, in typical points. The Schottky codes above are rigid in exactly the opposite way: by (O1)
and (O2), no long positive block ever reappears inverted.

*Remark 3 (why size and reversal must be combined).* One-wayness is not a size condition. The classes of Theorem 1
are small but one-way. The previous claim kills every positive-dimensional class whatever its support. Theorem A needs
only one of the two escapes, for one measure dominating the boundary class. What is left is a class with neither
escape.

*Remark 4 (the next test).* For a small, two-way class the shadow sum may diverge. For its Maharam extension, the
sharp return sum of the previous proof, Remark 3, is `sum_g a_U(g) a_V(g)`, where `a_W(g)` counts only points of
`W ∩ g^{-1} W` at which `|log D_g| <= R`. A certificate needs this sum to diverge. The natural small two-way candidate is
a reversal-symmetric block code: its blocks come in pairs `w`, `z w^{-1} z^{-1}` with `z` bounded. Deciding whether
some such code has divergent sharp sum is the named open step.

## Where the argument stops

- Theorem 2 needs a single one-way compact set carrying the whole class. A class that is two-way is not touched.
- Proposition 3.2 imports (Ol) and the standard Schottky and Morse estimates (S). Everything else is proved here.
- The free-group case is complete without (Ol).
