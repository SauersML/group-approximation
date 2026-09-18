---
rg: 2
id: ibn-failure-makes-rational-scalars-elementary
kind: claim
title: If R contains Q and R^m ≅ R^(m+k), then λ^k I_M is elementary for all λ in Q^x and every rank M = m'N with m' >= m, N >= 2, so those PE_M(R) are not finitely presented
distinct_from:
  leavitt-scalar-commutators-block-fp-central-quotients: that works at the level of unit groups containing the whole L_K(1,d)^x, and reaches E_N(R) only for d = 2 through GL_N(L_K(1,2)) = EL_N(L_K(1,2)); this proves elementarity of the rational scalars in E_N itself, for every d, and for every failure R^m ≅ R^(m+k) of the invariant basis number at any rank m.
  cone-sl2-and-v-put-central-scalars-in-derived-subgroup: that puts K^x into [H,H] for subgroups H of R^x containing V and a cone SL_2(K); this is the matrix statement λ^k I_M ∈ E_M(R) that the projective elementary route needs.
  rational-scalars-obstruct-fp-elementary-hosts: that shows a finitely presented PE_N(R) needs finitely generated elementary rational scalars; this shows that failure of the invariant basis number makes those scalars non-finitely generated.
---

**ESTABLISHED** by `ibn-failure-makes-rational-scalars-elementary-proof`
(lane proof, not independently reviewed; elementary; no novelty claimed).

## Statement

Let `R` be a nonzero unital ring with a unital map `Q -> R`. Suppose `R^m ≅ R^(m+k)`
as right `R`-modules for some `m, k >= 1`.

1. For every `m' >= m`, every `N >= 2` and every `λ ∈ Q^x`,
   `λ^k I_(m'N) ∈ E_(m'N)(R)`.
2. Hence for every rank `M = m'N` with `m' >= m`, `N >= 2` and `M >= 3`,
   `Λ_M(R) = {λ ∈ Q^x : λI_M ∈ E_M(R)}` contains `(Q^x)^k`. That group is not finitely
   generated. So `PE_M(R)` is **not finitely presented**, by
   `rational-scalars-obstruct-fp-elementary-hosts`, part 2.
3. **Leavitt families (`m = 1`).** If `R ≅ R^d` for some `d >= 2`, equivalently `R`
   contains `s_1..s_d, t_1..t_d` with `t_i s_j = δ_ij` and `Σ s_i t_i = 1`, then
   `λ^(d-1) I_N ∈ E_N(R)` for every `N >= 2`. For `d = 2`, every `λI_N` is
   elementary. So `PE_N(R)` is not finitely presented for any `N >= 3`.

Part 1 covers every even `M >= 2m`. It says nothing about ranks with no factorization
`m'N`, `m' >= m`, `N >= 2`, such as primes `M > m`, when `m >= 2`.

## Consequences for `q-algebra-with-fp-simple-projective-elementary-group`

- **Leavitt-type rings are excluded at every rank.** A ring host `R ⊇ Q` for the
  projective elementary route must satisfy `R ≇ R^d` for all `d >= 2`.
  - This covers the Leavitt resolvent ring `R_L` (its Attempt 3), every `B ⊗ L(1,d)`,
    and every ring with a unital Leavitt `(1,d)` family.
  - The restriction "no `R ≅ R^k`" in the search for a host is therefore forced, not a
    choice.
- **IBN failure at a higher rank kills an arithmetic progression of ranks.**
  `R^m ≅ R^(m+k)` rules out every rank `m'N` above.
- **Purely infinite simple rings (remark).** Ara–Goodearl–Pardo show that nonzero
  finitely generated projectives with equal `K_0` classes are isomorphic. This is recalled
  from memory, not re-read. Granting it, `R ≅ R^d` for some `d >= 2` holds exactly when
  `[1_R]` has finite order in `K_0(R)`. So a purely infinite simple host needs `[1_R]` of
  infinite order.
