---
rg: 2
id: kazhdan-isotypic-sectors-kernel-closure-proof
kind: route
title: Finitely many types per dimension, Malcev on the compact outer image, and Gelfand evaluation of the multiplicity unitaries
target: kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure
requires:
  - kazhdan-bounded-unitary-types-are-finite
  - finitely-generated-linear-groups-are-residually-finite
artifacts:
  - research/artifacts/rnorm-kazhdan-projection-sizes-2026-09-12.md
---

Notation as in the target. The full text is Section 1 of the artifact.

1. **Finite types.** `Irr_d(N)` is finite by `kazhdan-bounded-unitary-types-are-finite`.
   `G` acts on it by `g . [rho] = [rho o Ad(g^-1)]`. `N` acts trivially, because
   `rho o Ad(n^-1)` is conjugate to `rho` by `rho(n)`. So `Q` acts through a finite
   group, and that action is trivial. This is item 1.
2. **Invariance.** If `T : V_rho -> H` intertwines `rho` with `pi|_N`, then
   `pi(g) T` intertwines `rho o Ad(g^-1) ~ rho`. So `pi(g) H_rho = H_rho`. This is
   item 2.
3. **Splitting.** By Schur there is `U(g) in U(V_rho)`, unique up to scalars, with
   `rho(g n g^-1) = U(g) rho(n) U(g)^*`; take `U(n) = rho(n)`. Then
   `W(g) T := pi(g) T U(g)^*` is a unitary of `W_rho`, and
   `pi(g)|_(H_rho) = U(g) (x) W(g)`. Also `W(n) = 1`.
4. **Inner outer part.** Let `K` be the closure of `[rho(N)]` in `PU(V_rho)`.
   `[U(G)]` normalizes `K`, which gives a homomorphism `Q -> N(K)/K`.
   - `N(K)/K` is a compact Lie group, hence linear.
   - So the image of `Q` is a finitely generated linear group, hence residually
     finite (`finitely-generated-linear-groups-are-residually-finite`). It is
     therefore trivial, since `Q` has no nontrivial finite quotient.
   - So `[U(g)] in K`, and lifting gives `U(g) = lim lambda_k rho(n_k)`. This is
     item 3.
5. **Scalars at bounded multiplicity.** `A` commutes with `rho (x) 1`, so
   `A|_(H_rho) = 1 (x) A_rho` and `A_rho` commutes with `W(G)`.
   - The commutant of an abelian algebra is type I, and here the multiplicities
     are at most `m`. So `(A_rho|_E)' = (+)_(k <= m) M_k(Z_k)`, and this commutant
     contains `W(g)|_E`.
   - Evaluation at a character of `Z_k` is a `*`-homomorphism to `M_k(C)`. It
     turns `W` into a projective representation `Q -> PU(k)`, which is trivial as
     in step 4. So `W(g)|_E = lambda_g`, a central unitary.
   - For two characters `chi, chi'`, the cocycle cancels in
     `g -> lambda_g(chi)/lambda_g(chi')`. That is a homomorphism `Q -> T`, and it is
     trivial as in step 4, since `T` is compact Lie.
   - By Gelfand, `lambda_g` is constant.
6. **Finite families.** On `S`, `pi(g)|_S` and `pi(N)|_S` lie in the compact group
   `prod_i U(V_(rho_i)) (x) 1`, and `pi(G)|_S` normalizes the closure `L` of
   `T . pi(N)|_S`. The induced homomorphism `Q -> N(L)/L` lands in a compact Lie
   group, so it is trivial as in step 4. Hence `pi(g)|_S in L`. This is item 4.
