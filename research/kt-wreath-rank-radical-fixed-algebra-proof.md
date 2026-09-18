---
rg: 2
id: kt-wreath-rank-radical-fixed-algebra-proof
kind: route
title: Read the lamp measure off the rank of joint eigen-idempotents, and read rank-realized actions back as lamp models
target: kt-wreath-rank-radical-is-rank-fixed-algebra-rigidity
requires:
  - kun-thom-nonsofic-wreath
  - kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
  - sofic-groups-kill-rigid-compression-defects
---

Notation is as in the target. Throughout, `char k != 2`.

## 0. Rank facts

Let `R_omega = prod_omega M_(n_i)(k) / {rk = 0}` with `rk [x_i] = lim_omega rank(x_i)/n_i`, where
`omega` is a nonprincipal ultrafilter on `N`.

- **(R1)** `rk(x + y) <= rk x + rk y`, `rk(xy) <= min(rk x, rk y)`, and `rk(u x v) = rk x` for units `u, v`.
  The rank metric `d(x, y) = rk(x - y)` makes `R_omega` complete, since it is a metric
  ultraproduct of spaces of diameter at most 1. Multiplication is continuous:
  `rk(xy - x'y') <= rk(x - x') + rk(y - y')`.
- **(R2)** If `e, f` are idempotents with `ef = fe = 0`, then `rk(e + f) = rk e + rk f`.
  Extend `rk` to rectangular matrices over `R_omega` by the same ultralimit (still normalized
  by `n_i`). It is subadditive, satisfies `rk(XY) <= min(rk X, rk Y)`, and is additive on
  block-diagonal matrices, because the coordinatewise ranks are. Put `X = [e; f]` (a column)
  and `Y = [e  f]` (a row). Then `X(e + f) = X`, so `rk X <= rk(e + f)`, and `XY = diag(e, f)`,
  since `e^2 = e`, `f^2 = f` and `ef = fe = 0`. Hence
  `rk e + rk f = rk diag(e, f) = rk(XY) <= rk X <= rk(e + f)`. Subadditivity gives the reverse.
  (Representatives of `e, f` need not be exact idempotents, so this avoids passing to the limit.)
- **(R3)** If `e, f` are orthogonal idempotents, then `rk(e - f) = rk(e + f)`. Indeed
  `(e - f)^2 = e + f` and `(e - f)(e + f) = e - f`, and (R1) gives both inequalities.
- **(R4)** If `e, f` are commuting idempotents, then `rk(e - f) = rk(e + f - 2ef)`. Write
  `e - f = e(1 - f) - (1 - e)f`, a difference of orthogonal idempotents, and apply (R3)
  and (R2). Note that `e + f - 2ef` is the idempotent of the symmetric difference.
- **(R5)** If `u^2 = 1`, then `p = (1 - u)/2` is idempotent, `u = 1 - 2p` and `rk(u - 1) = rk p`,
  since 2 is a unit.
- **(R6)** A countable group is `k`-linear sofic iff it embeds in some `U(R_omega)`
  (Arzhantseva--Paunescu, with amplification). Subgroups and finite direct products of
  `k`-linear sofic groups are `k`-linear sofic (block sums). Hence, for countable `H`,
  `Rad_(rk,k)(H)` is the intersection of `ker theta` over all homomorphisms
  `theta : H -> U(R_omega)` and all rank ultraproducts.

## 1. Models give actions (Theorem 1)

Let `theta : W -> U(R_omega)` be a homomorphism, `u_x = theta(e_x)` and `p_x = (1 - u_x)/2`.
The `u_x` are commuting involutions, so the `p_x` are commuting idempotents (R5).

1. For finite `S` and a pattern `eps in 2^S` put
   `p_eps = prod_(x in S) p_x^(eps_x) (1 - p_x)^(1 - eps_x)`.
   These are orthogonal idempotents with sum 1, and `p_eps = p_(eps,0) + p_(eps,1)`
   when `S` grows by one point. So `E(C) = sum_(eps in C) p_eps` is a well-defined Boolean
   homomorphism from the clopen algebra of `2^X` to commuting idempotents.
2. By (R2), `nu(C) = rk E(C)` is a finitely additive probability on clopens. A countable
   disjoint union of clopens that is itself clopen is a finite union, by compactness. So
   `nu` is countably additive on the clopen algebra and extends uniquely to a Borel
   probability `mu_theta` (Caratheodory).
3. `theta(g) u_x theta(g)^(-1) = u_(gx)`, so `theta(g) E(C) theta(g)^(-1) = E(gC)`, where `(g omega)_(gx) = omega_x`.
   Rank is conjugation invariant (R1), so `mu_theta` is `G`-invariant.
4. By (R4), `rk(E(A) - E(B)) = rk E(A triangle B) = mu_theta(A triangle B)` for clopens `A, B`.
   So `E` is an isometry from the clopens, with the measure metric, into `(R_omega, d)`. In
   particular it is constant on null-equivalence classes.
5. Clopens are dense in `MALG(2^X, mu_theta)` and `R_omega` is complete (R1). So `E` extends to an
   isometry on `MALG`. The Boolean operations `A cap B -> E(A)E(B)` and `A^c -> 1 - E(A)` are
   continuous (R1), so the extension is a Boolean homomorphism. Limits of idempotents are
   idempotents, limits of commuting families commute, and equivariance passes to limits.
   So `(theta|_G, E)` is a `k`-rank realization of `G ↷ (2^X, mu_theta)`.
6. **Parity formula.** Let `f` be a lamp configuration with support `S`. Then
   `u_x p_eps = (-1)^(eps_x) p_eps`, so
   `theta(f) = prod_(x in S) u_x = sum_eps (-1)^(|eps|) p_eps = 1 - 2 E(odd_S)`.
   By (R5), `rk(theta(f) - 1) = mu_theta(odd_S)`.

## 2. Actions give models (Theorem 2)

Let `(sigma, E)` realize `G ↷ (Y, nu)` and let `pi : Y -> 2^X` be Borel and `G`-equivariant.

1. Put `q_x = E(pi^(-1){omega_x = 1})` and `u_x = 1 - 2 q_x`. These are commuting involutions.
2. By equivariance, `g pi^(-1){omega_x = 1} = pi^(-1){omega_(gx) = 1}`, so `sigma(g) u_x sigma(g)^(-1) = u_(gx)`.
3. So `theta(f, g) = (prod_(x in supp f) u_x) sigma(g)` respects the relations of the lamp group
   and of the semidirect product, and is a homomorphism `W -> U(R_omega)`.
4. Its eigen-idempotents are `p_x = q_x` and `p_eps = E(pi^(-1) C_eps)`. So `rk p_eps = nu(pi^(-1) C_eps)`,
   and `mu_theta = pi_* nu`.

## 3. Seed test (Theorem 3)

If `ao = o` then `m_a = 0` and both sides fail, so assume `ao != o`.

**If `m_a notin Rad_(rk,k)(W)`.** By (R6) some `theta` has `theta(m_a) != 1`. Take the realization
of Theorem 1 and `B = {omega_o = 1}`. For `gamma in Gamma`, `gamma B = {omega_(gamma o) = 1} = B`.
Also `aB = {omega_(ao) = 1}`, so `B triangle aB = odd_({o, ao})`. By the parity formula,
`mu_theta(B triangle aB) = rk(theta(m_a) - 1) > 0`.

**Conversely.** Let `(sigma, E)` realize `G ↷ (Y, nu)`, and let `B` be `Gamma`-invariant mod null
with `nu(aB triangle B) > 0`.

1. Replace `B` by `B' = intersect_(gamma in Gamma) gamma B`. This set is exactly `Gamma`-invariant, since
   `Gamma` is countable, and equals `B` mod null.
2. Define `pi(y)_(h Gamma) = 1_(B')(h^(-1) y)`. This is well defined because `B'` is `Gamma`-invariant.
   It is Borel, coordinate by coordinate. It is equivariant:
   `pi(gy)_(h Gamma) = 1_(B')(h^(-1) g y) = pi(y)_(g^(-1) h Gamma) = (g pi(y))_(h Gamma)`.
3. Let `theta` be the model of Theorem 2. We have `pi^(-1){omega_o = 1} = B'` and
   `pi^(-1){omega_(ao) = 1} = aB'`. So
   `rk(theta(m_a) - 1) = nu(pi^(-1) odd_({o, ao})) = nu(B' triangle aB') > 0`.
4. So `m_a notin ker theta`, and `m_a notin Rad_(rk,k)(W)` by (R6).

## 4. Radical formula (Theorem 4)

Let `sigma_G : G -> U(R_omega)` be injective. Composing it with `W -> G` kills exactly the lamp
group, so `Rad_(rk,k)(W)` consists of lamp configurations. For a lamp configuration `f` with
support `S`, the parity formula gives `theta(f) = 1` iff `mu_theta(odd_S) = 0`. Intersect over all `theta`.

## 5. Bernoulli normal form (Theorem 5)

**Lemma F (finitary form).** `mu in M_k` iff the following holds. For all finite `F subset W` and
`S subset X`, and all `eps > 0`, there are `n` and a map `phi : W -> M_n(k)` such that:

- `phi(1) = 1`;
- `rank(phi(vw) - phi(v)phi(w)) < eps n` for `v, w in F`;
- `|rank P_eta(phi) - n mu(C_eta)| < eps n` for every `T subset S` and every `eta in 2^T`, where
  `P_eta(phi) = prod_(x in T) ((1 - phi(e_x))/2)^(eta_x) ((1 + phi(e_x))/2)^(1 - eta_x)`.

*Proof.* (=>) Choose representatives `phi_i(w)` of `theta(w)`, with `phi_i(1) = 1`. The polynomial
`P_eta` commutes with the coordinatewise operations, so by Łoś the set of `i` satisfying the
finitely many conditions lies in `omega`, and in particular it is nonempty.

(<=) Exhaust `W` and `X` by finite sets `F_m, S_m`. Take `phi_m` for `(F_m, S_m, 1/m)`, fix any
nonprincipal ultrafilter `omega` on `N`, and set `theta(w) = [phi_m(w)]` in `prod_omega M_(n_m)(k)`.

- For fixed `v, w`, every `m` large enough satisfies the second condition. So `theta` is
  multiplicative and unital.
- `theta(w) theta(w^(-1)) = 1`, so the values are units.
- Every finite `S subset X` lies in `S_m` for all large `m`, and the third condition is imposed
  for every subset of `S_m`. So `rk P_eta(theta) = lim_omega rank P_eta(phi_m)/n_m = mu(C_eta)` for
  every cylinder.

So `mu_theta = mu`. QED.

The proof shows that every `mu in M_k` is realized over `(N, omega)` for any fixed nonprincipal
`omega`. From now on all models use one such `omega`.

**Closure properties.**

- **(a) `delta_0 in M_k`.** The trivial homomorphism has all `p_x = 0`.
- **(b) Averaging with `delta_0`.** Let `theta` live in `prod_omega M_(n_i)`, and put
  `theta'(w) = [diag(theta_i(w), 1)]` in `prod_omega M_(2 n_i)`. This is the block sum of
  `theta` with the trivial representation, so it is a homomorphism. It is well defined on
  rank-null classes because `rank(diag(x, 1) - diag(x', 1)) = rank(x - x')`. Its lamp idempotents
  are `diag(p_x, 0)`, so its joint eigen-idempotents are `diag(p_eps, delta_(eps,0) 1)`, of normalized
  rank `(rk p_eps + delta_(eps,0))/2`. So `mu_(theta') = (mu_theta + delta_0)/2`.
- **(c) XOR convolution.** Put `(theta (x) theta')(w) = [theta_i(w) (x) theta'_i(w)]` in
  `prod_omega M_(n_i n'_i)`.
  - This is well defined, since `rank((x - x') (x) y) <= rank(x - x') n'`.
  - It is a homomorphism, being a tensor product of representations.
  - Its lamp involutions are `u_x (x) u'_x`, whose joint eigen-idempotents are
    `p''_delta = sum_(eps + eps' = delta) p_eps (x) p'_(eps')`.
  - These summands are orthogonal and rank is multiplicative on tensors, so
    `rk p''_delta = sum mu(C_eps) mu'(C_(eps'))`.
  - So `mu_(theta (x) theta') = mu * mu'`, the pushforward of `mu x mu'` under coordinatewise XOR.
- **(d) Weak-* closure.** Let `mu_m -> mu` weak-*. Cylinders are clopen, so `mu_m(C) -> mu(C)`. Given
  `(F, S, eps)`, pick `m` with `|mu_m(C_eta) - mu(C_eta)| < eps/2` for every `eta`. Then apply Lemma F to `mu_m`
  with `eps/2`.

**Equivalences.** Let `G` be `k`-linear sofic, and let `beta` be the fair Bernoulli measure.

- **(W linear sofic => `beta in M_k`).**
  1. Take an injective `theta` (R6) and `mu = mu_theta`. The Fourier coefficient
     `mu^(S) = int (-1)^(sum_(x in S) omega_x) d mu = 1 - 2 mu(odd_S)` is `< 1` for every finite nonempty `S`,
     since `theta(f) != 1` for the configuration `f` with support `S`.
  2. By (b), `mu' = (mu + delta_0)/2 in M_k` has `mu'^(S) = (mu^(S) + 1)/2 in [0, 1)` for `S != empty`.
  3. By (c), the XOR powers `mu'^(*m)` lie in `M_k`, with Fourier coefficients `mu'^(S)^m`. These
     tend to `0` for `S != empty` and equal `1` for `S = empty`, which are the Fourier coefficients of `beta`.
  4. The characters span a dense subalgebra of `C(2^X)` (Stone--Weierstrass: they are real, contain
     `1`, are closed under products and separate points). So `mu'^(*m) -> beta` weak-*, and `beta in M_k` by (d).
- **(`beta in M_k` => W linear sofic).**
  1. Take `theta` with `mu_theta = beta`. Then `rk(theta(f) - 1) = beta(odd_S) = 1/2` for every nonzero
     configuration `f`.
  2. Let `sigma_G` be injective. The group `W` embeds in `theta(W) x sigma_G(G)` through
     `w -> (theta(w), sigma_G(bar w))`. If `bar w != 1` the second coordinate is nontrivial; otherwise
     `w` is a nonzero configuration and the first coordinate is nontrivial.
  3. Apply (R6).
- **(`beta in M_k` <=> the generalized Bernoulli action is rank-sofic).** Theorem 1 gives one
  direction. Theorem 2 with `pi = id` gives the other.

## 6. The Theorem E pair (Theorem 6)

By `kun-thom-nonsofic-wreath`, `Gamma` and `G` are residually finite Kazhdan groups and `Gamma` is
infranormal in `G`. So `G` is sofic, hence `k`-linear sofic (permutation matrices). Put `z = e_o`.
It commutes with `Gamma`, because `Gamma o = o`.

**Seed commutators.** For `g in G` and `gamma in Gamma`,
`[g z g^(-1), gamma] = e_(go) e_(gamma g o) = g . m_(g^(-1) gamma g)`, written additively in the lamps.

**Cocycle.** `m_(ab) = m_a + a . m_b`. `N` is generated by the conjugates `g^(-1) gamma g`. So a
`G`-invariant subgroup `U` of lamps contains every seed commutator iff it contains `m_n` for
every `n in N`.

**Fibre generation.** Two cosets `g Gamma` and `g' Gamma` lie in one `N`-fibre iff `g' = gn` with `n in N`.
Then `e_(g Gamma) + e_(g' Gamma) = g . m_n`. So `K_even` is the subgroup generated by
`{g . m_n : g in G, n in N}`, which is the smallest `G`-invariant subgroup containing every `m_n`.

**(i) => (iii).** Let `W/U` be `k`-linear sofic, with `U` a `G`-invariant subgroup of lamps. Then
`Rad_(rk,k)(W) <= U`, so `K_even <= U`. Every seed commutator `g . m_(g^(-1) gamma g)` lies in `K_even`, so
the seed defect in `W/U` is trivial.

**(iii) => (ii).** Suppose `RC_k` fails for a realized action `(Y, nu)`.

1. `L^inf(Y)^Gamma` is a von Neumann algebra generated by its projections. So some `Gamma`-invariant
   (mod null) `B` is not `N`-invariant: `nu(nB triangle B) > 0` for some `n in N`.
2. Build `pi`, `mu = pi_* nu` and `theta` as in Section 3. By the parity formula,
   `ker theta cap lamps = N_mu`.
3. `W/N_mu` embeds in `theta(W) x G` through `w -> (theta(w), bar w)`, so it is `k`-linear sofic (R6).
4. `m_n notin N_mu`, and `N_mu` is `G`-invariant because `mu` is. By the cocycle step, some seed
   commutator is nontrivial in `W/N_mu`. This contradicts (iii).

This also proves the addendum: `W/N_mu` contains `G`, since `N_mu <= lamps`, and it has a nontrivial
rigid defect `[g z g^(-1), gamma] != 1` with `z in C(Gamma)`. So it is not sofic by
`sofic-groups-kill-rigid-compression-defects`.

**(ii) => (i).**

- **`Rad_(rk,k)(W) <= K_even`.** Sofic groups are `k`-linear sofic, so
  `Rad_(rk,k)(W) <= Rad_sof(W) = K_even` (`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`).
- **`K_even <= Rad_(rk,k)(W)`.** Let `n in N`. If `m_n notin Rad_(rk,k)(W)`, Theorem 3 gives a realized
  action and a `Gamma`-invariant `B` with `nu(nB triangle B) > 0`. But `RC_k` makes `1_B` `N`-invariant.
  So every `m_n` lies in the radical, which is normal in `W`. By fibre generation, `K_even` lies in it.

**Equivalent form of (ii).** `L^inf^Gamma = L^inf^N` iff `L^inf^Gamma` is `G`-invariant. If it is
`G`-invariant, it is fixed by every `g Gamma g^(-1)` and hence by `N`. Conversely, `L^inf^N` is
`G`-invariant because `N` is normal.

## 7. Calibrations (remarks, not used above)

- **Sofic actions are rank-realized.**
  1. A sofic approximation of `G ↷ (Y, nu)` yields `sigma : G -> prod_omega Sym(n_i)` and a Boolean
     homomorphism `MALG -> prod_omega P([n_i])`. These are equivariant and preserve normalized
     counting measure modulo Hamming-null sets.
  2. Send permutations to permutation matrices and subsets to diagonal idempotents. Then
     `rank(P_s - P_t) <= #{i : s(i) != t(i)}`, so Hamming-null maps to rank-null.
  3. So `RC_k` contains Kun--Thom Theorem C for sofic actions, and Corollary D is its instance:
     `beta` is not in the Hamming analogue of `M_k`.
- **Profinite actions.** They satisfy (ii) for every realization, because the conclusion depends
  only on the action (`profinite-action-fixed-algebra-invariant`).
- **Characteristic two.** `u_x - 1` is nilpotent and (R5) fails, so the lamp measure is not defined.
  The theorem makes no claim there.
