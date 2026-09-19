---
rg: 2
id: correlated-products-cannot-substitute-rounds-for-alphabet
kind: claim
title: Unless P = NP, no route that outputs a correlated product of polynomial-time computed bipartite unique games -- heterogeneous factors, any coupling mu of their constraints whose coordinate marginals have density at most D, including expander-walk and derandomized tuple repetition and the diagonal coupling -- beats deficit ratio C_+ sqrt(1.5 ln K) against its union-bound completeness D eta_Sigma, because sdp+ tensorizes coupling-blindly and the base SDPs decide it; so sqrt-scale hardness at ratio C or UGC at (1 - eps, delta) this way needs base alphabet ln K >= C^2/12C_3 or (1-delta)^2/12C_3 eps
distinct_from:
  parallel-repetition-cannot-substitute-rounds-for-alphabet: that kills only the independent repetition G^l of one base game, through the imported composed bound (S1) for G^l; this kills every coupling mu with bounded coordinate densities and heterogeneous factors, by redoing the tensor step of sdp+ for mu-products. It closes that claim's first two listed survivors (heterogeneous products; derandomized or partial repetition) except fortification.
  steurer-parallel-repeated-unique-games-rounding: that is the imported bound for G^l; this proves the coupling-blind analogue for mu-products from the imported sdp+ statements, which that bound does not give (Lemma 9 there is for G^l only).
  steurer-hellinger-relaxation-rounding: that is the imported sdp+ theory (definition, Theorem 3, Theorem 8); this is the new tensor inequality for mu-products and its consequence for NP-hardness routes.
  expansion-certified-repetition-caps-deficit-ratio: that caps repetition routes whose soundness is certified by expansion rates; this bounds the true value of every mu-product NO output, whatever the soundness argument.
  sqrt-scale-unique-games-hardness: that is the open hole; this kills one more class of routes to it (bounded-base-alphabet correlated products).
artifacts:
  - experiments/ugc-correlated-product-rounding-2026-09-17/check_correlated_product_tensor.py
  - experiments/ugc-correlated-product-rounding-2026-09-17/output.txt
---

**ESTABLISHED (class kill, conditional on P != NP only through its
conclusion).** Proof: `correlated-products-cannot-substitute-rounds-for-alphabet-proof`.

## Setting

- **Games.** Unique games are bipartite, with rational weights, as in
  `sqrt-scale-unique-games-hardness`. `opt` is the value. `sdp` is the basic SDP
  of `steurer-parallel-repeated-unique-games-rounding`, and `sdp+` is the
  Hellinger value (H0) of `steurer-hellinger-relaxation-rounding`. `C_3 >= 1`
  is the constant of (H1) there. Put `C_+ := 2 sqrt(2 C_3)`, so that
  `1.5 C_+^2 = 12 C_3`. `ln` is the natural logarithm.
- **µ-products.** Let `G_1, ..., G_l` be bipartite unique games. Game `G_j` has
  left vertices `L_j`, right vertices `R_j`, alphabet `Σ_j` with
  `|Σ_j| = k_j >= 2`, and constraint distribution `w_j` on its constraint set
  `E_j`. Let `µ` be any probability distribution on `E_1 × ... × E_l`, and let
  `µ_j` be its `j`-th marginal. The **µ-product** `H = ⊗_µ (G_1, ..., G_l)` is
  the unique game with
  - left vertices `L_1 × ... × L_l`, right vertices `R_1 × ... × R_l`, and
    alphabet `Σ_1 × ... × Σ_l`;
  - one constraint `((u_j)_j, (v_j)_j, π_1 × ... × π_l)` of weight
    `µ(e_1, ..., e_l)` for each tuple `e_j = (u_j, v_j, π_j)`.

  The **coordinate density** of `µ` is `D := max_j max_(e in E_j) µ_j(e)/w_j(e)`.
  Note that `D >= 1`.
- **Examples.**
  - `µ = w^(⊗l)` for a single game `G` gives `G^l`, with `D = 1`.
  - `µ = w_1 ⊗ ... ⊗ w_l` gives the heterogeneous product, with `D = 1`.
  - Tuples sampled along a walk, stationary at `w`, on any graph on `E` (for
    example, expander-walk derandomized repetition) have `D = 1`.
  - A sampler whose coordinates are within a factor `D` of `w` has density `D`.
  - The diagonal `µ(e, ..., e) = w(e)` has `D = 1`.
  - Partial products are included: a factor may be a trivial game of deficit
    `0`.
- **Correlated-product route.** A polynomial-time map `x ↦ (G_(x,t), n_(x,t))`,
  for `t = 1..m_x`, where each `G_(x,t)` is a bipartite unique game with
  alphabet at most `K_x` and each `n_(x,t)` is a positive integer written in
  binary. The route outputs some µ-product `H_x` of the multiset of factors in
  which `G_(x,t)` appears `n_(x,t)` times. Here `l_x = Σ_t n_(x,t)`, and the
  coupling has coordinate density at most `D_x`. Neither `H_x` nor `µ` is
  required to be computable, and `D_x` and `K_x` need not be known.
- **Union-bound completeness.** A route has union-bound completeness `η_Σ`
  (a positive rational) if `x in Y ⇒ Σ_t n_(x,t) (1 − opt(G_(x,t))) <= η_Σ`. The product
  labelling then gives `opt(H_x) >= 1 − D_x η_Σ` (Theorem CP (a)). Call
  `η_cert := D_x η_Σ` the **certified completeness deficit**.

## Statements

**Theorem CP.**

- **(a) Coupling-blind tensor inequality; unconditional.** For every µ-product,
  with `D_j` the density of `µ_j` with respect to `w_j`,

  ```text
  sdp+(H)  >=  1 − Σ_j D_j (1 − sdp+(G_j)),        opt(H)  >=  1 − Σ_j D_j (1 − opt(G_j)).
  ```

- **(b) Rounding; unconditional.** With `D = max_j D_j` and `K = max_j k_j`,

  ```text
  opt(H)  >=  1 − C_+ sqrt( D · ln K · Σ_j (1 − sdp(G_j)) ).
  ```

  Only the base alphabets appear. The output alphabet `Π_j k_j`, the number of
  coordinates, and the correlations of `µ` beyond its marginals do not.
- **(c) Decision.** Take a correlated-product route with union-bound
  completeness `η_Σ` and `x in N ⇒ opt(H_x) <= 1 − Γ`, where
  `Γ > C_+ sqrt(1.5 D_x η_Σ ln K_x)` for every `x in N`. Then `Pi` is in `P`,
  decided by the base SDPs alone, without writing down `H_x` or `µ`.
- **(d) Ratio ceiling.** Suppose `D_x <= D` and `K_x <= K` on `N`. Then, unless
  `Pi` is in `P`,

  ```text
  Γ / sqrt(η_cert)  <=  C_+ sqrt(1.5 ln K)  =  sqrt(12 C_3 ln K),   where η_cert = D η_Σ,
  ```

  uniformly in `l`, in the number of distinct factors, and in `µ`.

**Corollary CP (unless P = NP).**

1. **Sqrt scale.** A correlated-product route that makes
   `Gap-UG[1 − η_cert, 1 − C sqrt(η_cert)]` NP-hard, with completeness
   certified by the union bound, needs base alphabet
   `ln K >= C^2 / (12 C_3)`.
2. **UGC.** A correlated-product route that makes `Gap-UG[1 − ε, δ]` NP-hard,
   with `η_cert <= ε`, needs `ln K >= (1 − δ)^2 / (12 C_3 ε)`.
3. **Consistency with the independent case.** For `µ = w^(⊗l)`, (c)
   specializes to Theorem RA (a) of
   `parallel-repetition-cannot-substitute-rounds-for-alphabet`, with `C_+` in
   place of `C_1` and `η_Σ = lη`.

## Class kill (impact type 3)

- **Invariant.** The invariant is the Hellinger deficit `1 − sdp+`. Under
  µ-products it is subadditive over coordinates, up to the coordinate density:
  (a). This holds for every coupling, because the tensor solution
  `⊗_j f^(j)_(u_j,i_j)` lives on the product probability space `Π_j Ω_j`,
  which is independent of `µ`. The per-constraint objective is a product of
  numbers in `[0, 1]`, and only its expectation under `µ` is taken, so `µ`
  enters through its marginals alone.
- **Where every member dies.** Members die at the soundness of the output.
  - On a NO output, `opt(H_x) <= 1 − Γ` with
    `Γ > C_+ sqrt(1.5 D η_Σ ln K)` forces `Σ_t n_t (1 − sdp(G_t)) > 1.5 η_Σ`.
  - On a YES output, `Σ_t n_t (1 − sdp(G_t)) <= η_Σ`.
  - Polynomially many base SDPs, each solved to precision `η_Σ/(3l)`, separate
    the two.
- **What is killed.** Every route to `sqrt-scale-unique-games-hardness` or to
  UGC of the form "NP-hard base family, then any bounded-density correlated
  product" with `ln K < C^2/(12 C_3)` (respectively
  `ln K < (1−δ)^2/(12 C_3 ε)`), whatever soundness argument is used. This
  includes:
  - independent, heterogeneous and partial repetition;
  - derandomized repetition by expander walks or samplers with bounded
    marginal distortion, in any variant whose output vertices are ordered
    tuples and whose output constraints are coordinatewise (whether a
    particular published derandomized repetition has this form is not checked
    here);
  - any mixture of these.

  The two survivors "heterogeneous products" and "derandomized or partial
  repetition" of `parallel-repetition-cannot-substitute-rounds-for-alphabet`
  are closed here, except for fortification.

## Checks

`experiments/ugc-correlated-product-rounding-2026-09-17/check_correlated_product_tensor.py`
writes `output.txt` and ends in ALL PASS. It checks, in exact rational
arithmetic, on random small µ-products (heterogeneous alphabets `(2,3)` and
`(2,2,3)`, `l = 2, 3`) with random couplings of density up to `1.6`:

- **T1.** Tensor feasibility on `Ω^l`.
- **T2.** Objective multiplicativity at every constraint, computed directly on
  `Ω^l`.
- **T3.** The inequality (a) at non-vacuous values.
- **T4.** Union-bound completeness, by brute-force `opt(H)`.
- **T6.** The diagonal coupling, where `1 − opt(H) < D η_Σ`.

It also illustrates (H2) (T5), which is imported and not checked.

## What is not covered (survivors)

- **Set-indexed direct products (IKW-style) and fortification.** The tensor
  needs every output vertex to be an ordered tuple with one coordinate per
  factor, and every output constraint to be coordinatewise. Unordered `l`-sets,
  and vertices that are subsets of varying size, break the indexing that makes
  (2.8) hold for the tensor.
- **Completeness better than the union bound.** Part (c) is stated with
  `η_Σ`. When `µ` is far from independent, `η_out = 1 − opt(H)` can be much
  smaller than `D η_Σ`. The diagonal coupling is an example (T6), and it has
  no soundness amplification either. A route that certifies completeness
  `η_out << D η_Σ` and soundness `Γ >> sqrt(η_out ln K)` is not excluded here.
  No analogue of Feige–Lovász (S2) for µ-products is known in this graph.
- **Unbounded coordinate density**, meaning a coupling that concentrates a
  coordinate on a vanishing part of `E_j`. In that case the right factor game
  is the reweighted game `(E_j, µ_j)`, and (a) applies with `D = 1` to it.
  But the base SDP to be solved is then that of the reweighted game, which the
  route must make computable.
- **Composition or alphabet reduction after the product.** The output is then
  no longer a µ-product.
- **Base alphabet already large.** Routes with `ln K >= C^2/(12 C_3)`.
