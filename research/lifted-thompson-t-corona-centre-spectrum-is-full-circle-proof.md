---
rg: 2
id: lifted-thompson-t-corona-centre-spectrum-is-full-circle-proof
kind: route
title: Untwist the central unitary by its own twelfth root, square the spectrum away with rho tensor conj(rho), and spread it round the circle with the dilation
target: lifted-thompson-t-corona-centre-spectrum-is-full-circle
requires:
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
  - funar-sergiescu-lifted-thompson-t-is-t311
  - lifted-thompson-t-perfect-centre-cubically-elliptic
---

Notation is as in the target.  Throughout, assume `G(eps_0)` and fix `alpha_0`.

## Preliminaries

**(P1) Exact lifting of finite-order unitaries.**  Let `u` be a unitary in a corona `Q`
with `u^m = 1`, and let `omega = e^(2 pi i/m)`.
- The elements `e_j = (1/m) sum_l omega^(-jl) u^l` are orthogonal projections summing
  to `1`, and `u = sum_j omega^j e_j`.
- Orthogonal families of projections summing to `1` lift to such families in
  `prod M_(k_n)`: lift `e_1, ..., e_(m-1)` successively into the complement of the
  previous lifts, and let `E_0` be the rest.
- Then `U_n = sum_j omega^j E_j^(n)` is a lift of `u` with `U_n^m = 1` exactly.
- For a word `w`, `||w(A) - 1||_Q = limsup_n ||w(A_n) - 1||` for any bounded lift, by the
  definition of the quotient norm.

**(P2) Gap in a corona.**  Let `A', B'` be unitaries in a corona `Q` with
`A'^4 = B'^3 = 1` and `max_i ||r_i(A',B') - 1||_Q < eps_0`.  Then `A' = B' = 1`.
- By (P1), choose lifts with `A_n^4 = B_n^3 = 1` exactly.
- Then `D(A_n, B_n) < eps_0` for all large `n`, so `(A_n, B_n) = (1,1)` by `G(eps_0)`.
  Blocks with `k_n = 0` are vacuous.
- Hence `A' = B' = 1` in `Q`.

**(P3) Abelian images are trivial.**  `T̄` is perfect (item 2 of
`lifted-thompson-t-perfect-centre-cubically-elliptic`).  So every homomorphism from `T̄`
to an abelian group is trivial.

**(P4) The dilation.**  For `g in T̄`, `lambda(g)(x) = g(2x)/2` again commutes with
`x -> x+1`, because `g(2x+2)/2 = g(2x)/2 + 1`.
- `lambda(g)` is piecewise linear, with dyadic breakpoints (those of `g`, halved), slopes
  powers of `2`, and it preserves `Z[1/2]`.  So it is the lift of an element of `T`, and
  lies in `T̄`.
- `lambda` is an injective homomorphism, and `lambda^k(z)` is the translation `t_k` by
  `2^(-k)`.

**(P5) Nontriviality survives dilation.**  If `rho` is nontrivial, so is `rho o lambda^k`.
- Let `N ⊴ T̄` be a normal subgroup.  Then `NZ/Z ⊴ T`, where `Z = <z>`, and `T` is simple
  (Cannon--Floyd--Parry Thm 5.8, cited in `thompson-t-has-full-mf-radical`).
  - If `NZ = T̄`, then `T̄ = [T̄, T̄] = [NZ, NZ] = [N, N] <= N`.
  - Otherwise `N <= Z`.
- The group `lambda^k(T̄)` is not contained in `Z`.  Indeed, `lambda^k(a)^4 = t_k` is
  translation by `2^(-k)`, which is not the fourth power `z^(4m)` of any element of `Z`.
- So if `ker rho` contains `lambda^k(T̄)`, then `ker rho = T̄`.

**(P6) Corners.**  Let `P` be a nonzero projection in `rho(T̄)' ∩ Q`.
- The map `rho_P(g) = P rho(g)` is a homomorphism into `U(PQP)`.
- `PQP` is a corona `prod M_(m_n) / (+)`, with `m_n` the ranks of lifted projections.
- If `P = chi_(S_1)(C)` for a clopen `S_1 ⊆ sp(C)`, then `P` lies in `C^*(C)`, which is
  contained in `rho(T̄)'`.  Also `sp_(PQP)(CP) = S_1`, via `C^*(C) = C(sp C)`.

## Item 1 (central twist lemma)

Let `sp(C)` lie in the arc `|theta| <= alpha`, with `alpha < alpha_0 <= pi`.
- Let `Theta = log C` by continuous functional calculus, with the branch cut at `-1`.
  Then `Theta` is self-adjoint, `e^(i Theta) = C`, `sp(Theta) ⊆ [-alpha, alpha]`, and
  `Theta` lies in `C^*(C)`, so it commutes with `rho(a)` and `rho(b)`.
- Put `u = e^(i Theta/12)`, `A' = rho(a) u^(-3)` and `B' = rho(b) u^(-4)`.  Since `u` commutes
  with `rho(T̄)` and `u^12 = C`:
  - `A'^4 = rho(a^4) u^(-12) = C C^(-1) = 1`;
  - `B'^3 = rho(b^3) u^(-12) = 1`.
- **The commutator relators.**  For `i = 1, 2`, `r_i` is a commutator, so its exponent sums
  in `a` and in `b` are both `0`.  Since `u` is central for `rho(T̄)`,
  `r_i(A', B') = r_i(rho(a), rho(b)) = rho(r_i(a,b)) = 1`, by
  `funar-sergiescu-lifted-thompson-t-is-t311`.
- **The pentagon.**  `(B'A')^5 = rho((ba)^5) u^(-35) = C^3 u^(-35) = u^(36-35) = u`, again by
  that presentation.  So
  `||r_P(A',B') - 1|| = ||u - 1|| <= max over |theta| <= alpha of |e^(i theta/12) - 1|`,
  which is `2 sin(alpha/24)`.
- `2 sin(alpha/24) < eps_0`, because `alpha < 24 arcsin(eps_0/2)`.
- By (P2), `A' = B' = 1`.  Then `rho(a) = u^3` and `rho(b) = u^4` commute.  Since `a, b`
  generate `T̄`, `rho(T̄)` is abelian, and `rho` is trivial by (P3).  ∎

## Item 2 (short pieces die)

Let `S_1` be clopen in `sp(C)` and contained in a closed arc
`{e^(i theta) : theta_1 <= theta <= theta_1 + L}` with `L < alpha_0`.  Let `P = chi_(S_1)(C)`.
If `P = 0`, then `S_1` is empty and there is nothing to prove.  Otherwise, by (P6),
`rho_P` is a corona representation in `Q_1 = PQP = prod M_(m_n)/(+)`.

**Tensoring with the conjugate.**  Let `Q_2 = prod M_(m_n^2) / (+)`.
- `Phi([x_n]) = [x_n ⊗ 1]` is a unital *-homomorphism `Q_1 -> Q_2`.
- `Psi([y_n]) = [1 ⊗ conj(y_n)]`, with entrywise complex conjugation, is conjugate-linear,
  multiplicative, *-preserving and unital.
- Both maps are well defined, because they preserve null sequences.  Their ranges commute.
- So `sigma(g) = Phi(rho_P(g)) Psi(rho_P(g))` is a homomorphism `T̄ -> U(Q_2)`.

**The spectrum of `sigma(z)`.**
- `sigma(z) = Phi(CP) Psi(CP)` is a product of two commuting unitaries.
- `sp(Phi(CP)) ⊆ S_1`, and `sp(Psi(CP)) ⊆ conj(S_1)`, since
  `Psi(CP) - mu = Psi(CP - conj(mu))`.
- In the commutative C*-algebra they generate,
  `sp(sigma(z)) ⊆ S_1 · conj(S_1) ⊆ {e^(i theta) : |theta| <= L}`.

**Conclusion.**
- Item 1, applied to `sigma` with `alpha = L`, shows that `sigma` is trivial.
- Fix `g` and let `v_n` be unitary lifts of `rho_P(g)`, with eigenvalues `mu_i^(n)`.
  Then `||v_n ⊗ conj(v_n) - 1|| -> 0`.  Since `v_n ⊗ conj(v_n)` is normal with
  eigenvalues `mu_i conj(mu_j)`, we get `max_(i,j) |mu_i^(n) - mu_j^(n)| -> 0`.  So
  `||v_n - mu_1^(n) 1|| -> 0`.
- Hence `rho_P(g)` is a scalar sequence, which is central in `Q_1`.  So `rho_P(T̄)` is
  abelian and `rho_P` is trivial by (P3).  That is, `P rho(g) = P` for all `g`.
- In particular `CP = P`, so `S_1 = sp_(Q_1)(CP) ⊆ {1}`.

**Components.**  Let `K_0` be a component of `sp(C)`.  It is a point, an arc or the whole
circle.  Suppose `K_0 != {1}` and `K_0` is an arc or point of length `< alpha_0`.
- Choose an open arc `U ⊇ K_0` of length `< alpha_0`.
- In a compact Hausdorff space a component is the intersection of the clopen sets that
  contain it.  By compactness, some clopen `W` has `K_0 ⊆ W ⊆ U`.
- By the above, `W ⊆ {1}`, which contradicts `K_0 != {1}`.

So every component other than `{1}` has length `>= alpha_0`.  ∎

## Item 3 (full circle at every level)

Let `rho` be nontrivial and fix `k >= 0`.  Choose `j` with `2^j alpha_0 >= 2 pi`, and put
`m = k + j`.

**The level-`m` spectrum contains a long arc.**
- `sigma_m = rho o lambda^m` is a corona representation of `T̄`, and it is nontrivial by
  (P5).  Its central unitary is `sigma_m(z) = rho(t_m)`.  Let `S_m = sp(rho(t_m))`.
- If `S_m ⊆ {1}`, then `sigma_m(z) = 1`, and item 1 (with `alpha = 0`) makes `sigma_m`
  trivial, a contradiction.
- So, by item 2 applied to `sigma_m`, `S_m` has a component that is an arc of length
  `>= alpha_0`, or is the whole circle.

**Pushing down to level `k`.**
- `t_k = t_m^(2^j)`, so `sp(rho(t_k)) = {w^(2^j) : w in S_m}` by spectral mapping.
- The map `w -> w^(2^j)` sends an arc of length `>= alpha_0` onto `S^1`, because
  `2^j alpha_0 >= 2 pi`.
- Hence `sp(rho(t_k)) = S^1`.  ∎

## Item 4 (corners, and the levelwise form)

**Corners.**
- For a nonzero `P` in `rho(T̄)' ∩ Q` with `rho_P` nontrivial, `rho_P` is a nontrivial
  corona representation by (P6).  Item 3 then gives `sp_(PQP)(CP) = S^1`.
- For `P` in `rho(lambda^k T̄)' ∩ Q`, apply the same argument to `rho o lambda^k`, whose
  central unitary is `rho(t_k)`.
- A central projection `[chi_N']` of `Q` lies in every relative commutant, and its corner
  is the corona over the subsequence `N'`.

**Levelwise form.**  Suppose the conclusion fails.
- Then there are `delta > 0`, an infinite `N_1 ⊆ N''` and points `mu_n` with
  `dist(mu_n, sp(c_n)) >= delta` for all `n` in `N_1`.
- Pass to an infinite `N_2 ⊆ N_1` along which `mu_n -> mu`.  Then
  `dist(mu, sp(c_n)) >= delta/2` for all large `n` in `N_2`, so
  `||(c_n - mu)^(-1)|| <= 2/delta` there, since `c_n` is normal.
- Let `P = [chi_(N_2)]`, a central projection.
  - `mu` is not in `sp_(PQP)(CP)`.
  - But `rho_P` is nontrivial, because `||rho_P(g) - P|| = limsup over N_2 of ||u_n(g) - 1||`,
    which is at least `c`.
- This contradicts the corner statement.
- The same argument with `rho o lambda^k` gives the statement for `rho(t_k)`.  ∎

## Item 5 (class kill)

**Untensored.**
- By item 3, `C^*(C) = C(S^1)`, with `C` corresponding to the identity function.  `S^1` is
  connected, so there is no projection other than `0` and `1`.
- A unitary `u = f(C)` with `u^12 = C` is a continuous `f : S^1 -> S^1` with
  `f(w)^12 = w`.  Then `12 deg f = deg(id) = 1`, which is impossible.

**Tensored.**
- Let `sigma = rho^(⊗p) ⊗ conj(rho)^(⊗q)`, built as in item 2 from the maps
  `Phi` and `Psi` placed on the individual tensor legs.  It is a corona representation of
  `T̄` in matrix size `k_n^(p+q)`.
- The legs `C_1, ..., C_(p+q)` commute, and `sigma(z) = C_1 ... C_(p+q)`.
- Choose `g` and `c > 0` with `N''` infinite.  This is possible because `rho` is nontrivial.
  By the levelwise form of item 4, `sp(c_n)` becomes `eps`-dense along `N''` for every
  `eps > 0`.  So the level-`n` joint spectrum of the lifted legs,
  `sp(c_n)^p × conj(sp(c_n))^q`, becomes `eps`-dense in `(S^1)^(p+q)`.
- The joint spectrum of `(C_1, ..., C_(p+q))` in the corona contains every point that is a
  limit along a subsequence of level-`n` joint spectral points.  Hence it is all of
  `(S^1)^(p+q)`, and
  `C^*(C_1, ..., C_(p+q)) = C((S^1)^(p+q))`.
- In this algebra `sigma(z)` is the function `(w_1, ..., w_(p+q)) -> w_1 ... w_p conj(w_(p+1) ... w_(p+q))`.
  Its class in `H^1((S^1)^(p+q); Z) = Z^(p+q)` is `(1, ..., 1, -1, ..., -1)`.
- A twelfth root `u = f(C_1, ...)` would have a class `d` with `12 d = (1, ..., -1)`, which
  is impossible.  ∎

**Why this is the failure step of the twist.**  Item 1 needs `u` central for `rho(T̄)` with
`u^12 = C` and `||u - 1|| < eps_0`.
- For any `u` with `u^12 = C` and `||u - 1|| < eps_0`, the spectrum `sp(u)` lies in the arc
  `|theta| < 2 arcsin(eps_0/2)`.
- So `sp(C) = sp(u)^12` lies in an arc of half-width `24 arcsin(eps_0/2)`, and the twist
  reaches no other `rho`.  In that range `rho` is already trivial, by items 1 and 3.
- The exponent bookkeeping is forced by the presentation.
  - `a^4 = b^3 = z` forces `A' = rho(a) u^(-3)` and `B' = rho(b) u^(-4)`.
  - Then `(B'A')^5 = C^3 u^(-35) = u^(36-35)`.
  - The residual exponent `36 - 35 = 1` is `12 * 3 - 15 - 20`, the Euler number of `T̄`
    (`funar-sergiescu-lifted-thompson-t-is-t311`).

With Euler number `0` the pentagon would be untwisted exactly.  With Euler number `1` the
twist costs `||u - 1||`, and on the full-circle representations of item 3 it cannot be
paid.
