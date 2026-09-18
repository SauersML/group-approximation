---
rg: 2
id: leavitt-scalar-commutators-block-fp-central-quotients-proof
kind: route
title: A finitely generated cover of a finitely presented central quotient contains the commutator subgroup, whose central part is then finitely generated
target: leavitt-scalar-commutators-block-fp-central-quotients
requires:
  - leavitt-unit-groups-over-every-field-are-simple-mod-scalars
  - leavitt-gl-equals-el-and-perfect-unit-group
  - agp-purely-infinite-simple-k1-is-unit-abelianization
  - abc-leavitt-path-k-theory-exact-sequence
---

Lane proof, not independently reviewed.

**0. Group lemma.**
- **A finitely generated cover.** Suppose `H/C` is finitely presented, with
  `C_0 ≤ C ≤ Z(H)`. Then `H/C` is finitely generated, so there is a finitely
  generated `H_0 ≤ H` with `H = H_0 C`.
- **It contains the commutators.** `C` is central, so
  `[h_1 c_1, h_2 c_2] = [h_1, h_2]`. Hence `[H,H] = [H_0,H_0] ≤ H_0`, and
  `C_0 ≤ H_0 ∩ C`.
- **A central kernel.** `H_0/(H_0 ∩ C) ≅ H_0 C/C = H/C` is finitely presented. Let
  `F` be free on a finite generating set of `H_0`. The kernel of `F -> H_0/(H_0 ∩ C)`
  is the normal closure of finitely many elements `r_1, ..., r_k`, because finite
  presentability does not depend on the finite generating set. That kernel maps onto
  `H_0 ∩ C`, so `H_0 ∩ C` is the normal closure in `H_0` of the images of the
  `r_i`. These are central in `H_0`, so their normal closure is the subgroup they
  generate, and `H_0 ∩ C` is finitely generated.
- **Contradiction.** `H_0 ∩ C` is abelian and finitely generated, so its subgroup
  `C_0` is finitely generated, contrary to hypothesis.

**1. Leavitt families.**
- **The Leavitt copy.** `K` is central, so `s_i -> s_i`, `t_i -> t_i` defines a unital
  `K`-algebra map `L_K(1,d) -> R`. `L_K(1,d)` is simple (Ara–Goodearl–Pardo,
  Theorem 4.2, as recorded in `agp-purely-infinite-simple-k1-is-unit-abelianization`)
  and the map is nonzero, so it is injective. Hence `U_d = L_K(1,d)^x ≤ R^x`.
- **C_0 is central.** It is central in `R^x`, hence in every `H ≤ R^x` that
  contains it.
- **C_0 ≤ [U_d, U_d].** By `abc-leavitt-path-k-theory-exact-sequence` (Corollary
  7.7, the rose with `d` petals, `k = K` a field),
  `K_1(L_K(1,d)) = coker(K_1(K) --(1-d)--> K_1(K)) = K^x/(K^x)^(d-1)`, through the
  natural map `K^x = K_1(K) -> K_1(L_K(1,d))`. So `λ^(d-1)` has trivial class. By
  `agp-purely-infinite-simple-k1-is-unit-abelianization`,
  `K_1(L_K(1,d)) = U_d^ab`, so `λ^(d-1)·1 ∈ [U_d, U_d] ≤ [H,H]`.
  - For `d = 2` this is also part 1 of
    `leavitt-unit-groups-over-every-field-are-simple-mod-scalars`: `U_2` is perfect.
- **C_0 is not finitely generated.** An infinite field `K` has a multiplicative group
  that is not finitely generated:
  - in characteristic `0`, `K^x` contains `Q^x`, which contains the free abelian group
    on the primes;
  - in characteristic `p`, either `K` is algebraic over `F_p`, and then `K^x` is an
    infinite torsion group; or `K` contains `F_p(t)`, and `F_p(t)^x` contains the
    free abelian group on the monic irreducible polynomials.

  In each case the subgroup cannot lie in a finitely generated abelian group.

  The map `λ -> λ^(d-1)` has finite kernel `μ_(d-1)(K)`. So `C_0 ≅ K^x/μ_(d-1)(K)`
  is not finitely generated either.
- Now apply part 0.

**2. Instances.**
- `H = R^x` contains `U_d`, so part 1 applies to it.
- For `H = [R^x, R^x]` and `d = 2`: `U_2` is perfect, so
  `U_2 = [U_2, U_2] <= [R^x, R^x] = H`. Then `C_0 = K^x <= U_2 = [U_2, U_2] <= [H, H]`,
  and part 0 applies. For `d >= 3` this step would need `C_0 <= [[R^x,R^x],[R^x,R^x]]`,
  which is not proved here, so that bullet is claimed only for `d = 2`.
- **E_N(R), d = 2.** `GL_N(L_K(1,2)) = EL_N(L_K(1,2))` for every `N >= 2`
  (`leavitt-gl-equals-el-and-perfect-unit-group`), and this group is `≅ L_K(1,2)^x`,
  so it is perfect. It contains the scalar matrices `λ I_N`, which are central in
  `GL_N(R)`. So `λ I_N ∈ [E_N(R), E_N(R)] ∩ Z(E_N(R))`, and part 0 applies to
  `E_N(R)`.
