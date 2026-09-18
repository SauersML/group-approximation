---
rg: 2
id: kun-thom-actor-atiyah-formal-torus-proof
kind: route
title: Complete the Laurent ring to the formal torus, truncate u-adically, and approximate by torsion-free p-adic analytic quotients
target: kun-thom-actor-strong-atiyah-via-formal-torus
requires:
  - char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup
  - p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah
artifacts:
  - experiments/kun-thom-formal-torus-2026-09-17/check_formal_torus.py
---

Notation as in [[kun-thom-actor-strong-atiyah-via-formal-torus]]. Put
`Lambda = Z_p[[u_1..u_d]]`, `J = (u_1,...,u_d)`, `m = (p) + J`, and
`Lambda_n = Lambda / J^n`. As a `Z_p`-module, `Lambda_n` is free with basis the
monomials `u^a` with `|a| < n`.

## Step 1: the substitutions

* **Binomial powers.** For `a in Z_p` and `t in J`, set
  `(1+t)^a = sum_(k >= 0) binom(a,k) t^k`. Here `binom(a,k) in Z_p`, since
  `binom(.,k)` maps `Z` to `Z` and is continuous. The series converges
  `J`-adically. The identities `(1+t)^(a+b) = (1+t)^a (1+t)^b` and
  `((1+t)^a)^b = (1+t)^(ab)` hold for integers, and each coefficient of
  `u`-degree `< n` is a polynomial in `a, b` with rational coefficients. So they
  hold for all `a, b in Z_p`.
* **The endomorphism.** For `A in SL_d(Z_p)` put
  `T_i = prod_j (1+u_j)^(A_ji) - 1`, which lies in `J`. Substitution
  `u_i -> T_i` defines a ring endomorphism `sigma_A` of `Lambda`. The
  coefficient of `u^a` in `f(T)` depends polynomially on finitely many
  coefficients of `f`. `sigma_A(J) <= J`, hence `sigma_A(J^n) <= J^n` and
  `sigma_A(m) <= m`.
* **Action on monomials.** For `w in Z_p^d` write `(1+u)^w = prod_i (1+u_i)^(w_i)`.
  Then `sigma_A((1+u)^w) = (1+u)^(A w)`. For the generators:
  `sigma_A(1+u_i) = (1+u)^(A e_i)`. Multiplicativity and the power identities
  above give the general case.
* **Cocycle.** `sigma_A sigma_B (1+u_i) = sigma_A((1+u)^(B e_i)) = (1+u)^(AB e_i)`.
  So `sigma_A sigma_B = sigma_AB`, and `sigma_A` is an automorphism with inverse
  `sigma_(A^-1)`. It preserves every `J^n`, so it descends to automorphisms
  `sigma_A^(n)` of `Lambda_n`.
* **Continuity.** The coefficients of `sigma_A^(n)` in the monomial basis are
  polynomials, with rational coefficients, in the entries of `A`. So
  `SL_d(Z_p) x Lambda_n -> Lambda_n` is continuous.

## Step 2: the embedding of H

* **`iota` is injective.** `x_i -> 1 + u_i` sends `Z[x]` isomorphically onto
  `Z[u] <= Lambda`, and `1 + u_i` is a unit of `Lambda`. So `iota` extends to
  `R = Z[x][x^-1]`. A Laurent polynomial `f` with `iota(f) = 0` has
  `x^c f in Z[x]` for some `c`, with `iota(x^c f) = 0`, so `f = 0`.
* **Intertwining.** `iota(alpha_A(x^v)) = iota(x^(Av)) = (1+u)^(Av) = sigma_A((1+u)^v) = sigma_A(iota(x^v))`,
  for `A in SL_d(Z)`.
* **Homomorphism.** Put `phi(M, A) = (iota(M), A)`. Then
  `phi((M,A)(M',A')) = (iota(M) iota(alpha_A(M')), AA') = (iota(M) sigma_A(iota(M')), AA') = phi(M,A) phi(M',A')`.
  `phi` is injective because `iota` is.
* **Congruence.** The constant term of `iota(f)` is `f(1,...,1)`. For `M in K`,
  `M(1) = I mod p`. So `iota(M) = I mod m`, and `phi(H) <= W = (I + M_r(m)) semidirect Gammahat_d(p)`.
  - `I + M_r(m)` is a group: `Lambda` is complete local, so a matrix congruent
    to `I` mod `m` is invertible with inverse congruent to `I`.
  - It is `sigma`-stable by Step 1.
  - `Gamma_d(p) <= Gammahat_d(p)`.

## Step 3: the quotients Q_n

* **Definition.** Let `G_n = ker( GL_r(Lambda_n) -> GL_r(F_p) )`, the matrices
  congruent to `I` mod `m`. Let `Q_n = G_n semidirect Gammahat_d(p)`, acting
  through `sigma^(n)`. Reduction mod `J^n` gives a homomorphism
  `pi_n : W -> Q_n` that is the identity on the second coordinate. Let `N_n`
  be its kernel.
* **The chain.** `N_n = { (g, I) : g = I mod J^n }`, so the `N_n` decrease.
  Their intersection is trivial, since the intersection of the `J^n` is `0`.
  The script (check 4) confirms the chain is strict on `phi(H)`, with
  `e_12(p (x_1 - 1)^n)`.
* **Compact `p`-adic analytic.**
  - `Lambda_n ≅ Z_p^N` with `N` finite, and multiplication is `Z_p`-bilinear.
    So `GL_r(Lambda_n)` is a closed subgroup of `GL_(rN)(Z_p)`, acting on
    `Lambda_n^r`, and `G_n` is a closed, hence compact `p`-adic analytic,
    subgroup (Cartan's closed subgroup theorem).
  - `Gammahat_d(p)` is an open subgroup of `SL_d(Z_p)`.
  - The action is continuous, so `Q_n` is a compact topological group with
    closed normal subgroup `G_n` and quotient `Gammahat_d(p)`.
  - By Lemma 2.12 of Fisher--Ng, arXiv:2606.19606 (the extension property of
    `p`-adic analytic groups), `Q_n` is `p`-adic analytic.
* **Pro-`p`.** Let `I_n` be the image of `m` in `Lambda_n / p^k`. It is
  nilpotent, and `p I_n^i <= I_n^(i+1)`. So the congruence kernel of
  `GL_r(Lambda_n / p^k)` has the filtration `I + M_r(I_n^i)`, whose successive
  quotients `M_r(I_n^i / I_n^(i+1))` are elementary abelian `p`-groups.
  - So `G_n`, an inverse limit over `k`, is pro-`p`.
  - `Gammahat_d(p)` is pro-`p` for the same reason.
  - Extensions of pro-`p` groups are pro-`p`, so `Q_n` is pro-`p`.

## Step 4: Q_n and W are torsion-free for p >= 3

A torsion element of a pro-`p` group has `p`-power order, so a nontrivial
torsion element has a power of order exactly `p`. Let `q = (g, A) in Q_n` have
`q^p = 1`.

1. **The acting part.** `A^p = I` in `Gammahat_d(p) <= CS(1,d,p)`, which is
   torsion-free for odd `p` (Minkowski, as used in
   [[p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah]]). So `A = I`,
   and then `q^p = (g^p, I)`.
2. **Modulo `J`.** Reduce `g` mod `J`: `g_0 in GL_r(Z_p)` with `g_0 = I mod p`
   and `g_0^p = I`. `CS(1,r,p)` is torsion-free for odd `p`, so `g_0 = I`, and
   `g = I + X` with `X in M_r(J)`.
3. **Leading form.** Suppose `X != 0` in `M_r(Lambda_n)`. Let `k` be the least
   `u`-degree occurring in `X`, with `1 <= k < n`, and let `X_k` be the
   homogeneous degree-`k` part.
   - `g^p - I = p X + binom(p,2) X^2 + ... + X^p`.
   - The term `X^j` has no monomials of degree `< jk`, and `jk > k` for `j >= 2`.
   - So the degree-`k` part of `g^p - I` is `p X_k`.
   - `Lambda_n` is torsion-free over `Z_p` with the monomial basis, so
     `p X_k = 0` forces `X_k = 0`. Contradiction.

   So `X = 0` and `q = 1`. This step uses no hypothesis on `p` (check 5 of the
   script runs it for `p = 2` and `p = 3`).
4. **`W` is torsion-free.** If `w in W` has finite order, so does each `pi_n(w)`.
   Hence `pi_n(w) = 1` for all `n`, and `w` lies in every `N_n`, so `w = 1`.

## Step 5: Strong Atiyah

Let `S <= W` be a finitely generated subgroup. Put `S_n = S cap N_n`.

* `S = S_1 >= S_2 >= ...` is a chain of normal subgroups of `S` with trivial
  intersection.
* `S / S_n` embeds in `Q_n`, a torsion-free compact `p`-adic analytic group. By
  [[p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah]], item 1, which
  covers every abstract subgroup, `S / S_n` is torsion-free and satisfies Strong
  Atiyah over `C`.
* `S / S_n` is a subgroup of a profinite group, hence residually finite, hence
  sofic.

By Jaikin-Zapirain's approximation theorem in the form of Fisher--Ng,
arXiv:2606.19606, Theorem 2.5 ("Let `G` be a finitely generated group and let
`G = G_1 >= G_2 >= ...` be a residual normal chain such that every quotient
`G/G_k` is sofic. If `A` is a finite matrix over `C[G]`, then
`rk_(N(G))(A) = lim_k rk_(N(G/G_k))(A_k)`"), every rank over `C[S]` is a limit of
integers, hence an integer. This is Corollary 2.6 of the same paper.

**Passage to all countable subgroups.** For a countable `S <= W` and a matrix
`A` over `C[S]`, let `S_0` be the subgroup generated by the finite support of
`A`. Induction from `S_0` to `S` preserves von Neumann ranks, so
`rk_(N(S))(A) = rk_(N(S_0))(A) in Z`.

With Step 2, this proves items 1-3 for `H ≅ phi(H)`.

**Zero divisors.** Let `k` have characteristic `0` and `ab = 0` in `k[H]`. The
coefficients generate a finitely generated field, which embeds in `C`. For
nonzero `a`, integrality of `rk(r_a)`, together with injectivity of `r_a` on
`C[H]` away from rank zero, gives `b = 0`. This is the argument of
[[two-variable-kun-thom-actor-atiyah-proof]], Step 3.

## Step 6: the ambient actor (item 4)

The map `(M, A) -> (M(1) mod p, A mod p)` is a homomorphism
`G_0 -> SL_r(F_p) x SL_d(F_p)`, because evaluation at `x = 1` commutes with
every `alpha_A`.

* It is surjective: elementary matrices generate `SL_r(F_p)`, and
  `SL_d(Z) -> SL_d(F_p)` is onto.
* Its kernel is `H`.

For a matrix `A` over `C[G_0]`, restriction to `H` multiplies sizes by
`[G_0 : H]` and gives `rk_(N(G_0))(A) = rk_(N(H))(res A) / [G_0 : H]`.

## Where each hypothesis enters

* `p >= 3`: Step 4, parts 1 and 2, and nowhere else.
* **The filtration.** `iota^-1(J^n) = I^n`, where `I = (x_1 - 1, ..., x_d - 1)`
  is the augmentation ideal. Every `alpha_A` fixes the point `x = 1`, so these
  powers are `SL_d(Z)`-stable. They have trivial intersection, and
  `R / I^n ≅ Z[u]/(u)^n` has finite `Z`-rank. The image of `H` in
  `GL_r(R/I^n) semidirect Gamma_d(p)` is therefore an arithmetic-type group.
  `p`-adic completion places it in the compact `p`-adic analytic group `Q_n`,
  where the Farkas--Linnell import applies.
* **Contrast with the `d = 2` proof.** There the variables were specialized to
  independent `p`-adic units. That specialization is injective on `K` but not
  equivariant, so the acting group had to be removed by a separate extension
  theorem. The augmentation filtration is equivariant but not injective at any
  finite stage, so the approximation theorem is needed instead.
* **Completion.** It is used only to make the quotients compact, which the
  import needs.
* Finite generation in Theorem 2.5: removed by the support argument in Step 5.
