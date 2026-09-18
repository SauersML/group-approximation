---
rg: 2
id: rf-weak-bass-defect-is-degree-two-approximation-defect
kind: claim
title: Over a residually finite group the weak-Bass defect of a big projective of finite rational rank is nonnegative and equals its Lück-approximation defect; for amenable groups of cd 2 it is lim b_2(N_i)/[K:N_i], so Kropholler's question for residually finite groups is Lück approximation in degree 2, and an L2-Swan step through an amenable quotient only moves the defect
distinct_from:
  l2-finite-projectives-over-amenable-groups-satisfy-weak-bass: that is the open inequality D(C) <= 0; this proves the reverse inequality D(C) >= 0 over residually finite groups and identifies D(C) with the failure of Lück approximation for C, so over residually finite groups the open inequality is an approximation statement
  flat-weak-bass-holds-exactly-for-locally-indicable-groups: that uses Swan's theorem to pass weak Bass up finite index; this uses Swan's theorem together with Bass's big-projectives theorem on every finite quotient at once, and combines it with Lück approximation
  amenable-cd-two-bass-defect-equals-euler-characteristic: item 3(c) there computes D(res_N P) only for groups without free subsemigroups; this proves chi_Q(N) = [K:N] chi_Q(K) for every finitely generated group of cd 2 with b_2 finite, and shows D(P) = lim b_2(N_i)/[K:N_i] in the residually finite amenable case
  amenable-cd-two-groups-have-an-l2-rank-gap: that records no result for residually finite groups; this reduces the residually finite case, in both directions, to Lück approximation of b_2 along a residual chain
---

**ESTABLISHED** (proposed; referee pending) through
`rf-weak-bass-defect-is-degree-two-approximation-defect-proof`, from
`amenable-cd-two-bass-defect-equals-euler-characteristic` (item 1),
`amenable-cd-two-kropholler-iff-locally-indicable` (items 2 and 3(i)) and
`flat-weak-bass-holds-exactly-for-locally-indicable-groups` (§4(c) of its proof). Recalled
imports: Bass's theorem that non-finitely-generated projective `Z[F]`-modules are free (`F`
finite; Bass 1963); Swan's theorem that `Q ⊗ P` is `Q[F]`-free for finitely generated projective
`Z[F]`-modules `P` (Swan 1960); Lück's approximation theorem for matrices over `Q[K]` along a
residual chain (Lück 1994); additivity and cofinality of `dim_U`; vanishing of `L²`-Betti numbers
of infinite amenable groups (Cheeger–Gromov); Kropholler–Linnell–Lück (a finitely generated
elementary amenable group of cd 2 is `BS(1,m)`, `m ≠ 0`).

**Notation.** `K` is a group, `U = U(K)`, `⊗ = ⊗_{Z[K]}`. `C` is a countably generated projective
`Z[K]`-module, written `C = Z[K]^(ℕ) E` for a row-finite idempotent matrix `E` acting by right
multiplication. `A_m` is the matrix of the first `m` rows of `E`. Put

> `r(C) = rank_Q(Q ⊗ C)`, `d(C) = dim_U(U ⊗ C)`, `D(C) = r(C) − d(C)` (the Bass defect).

For a finite quotient `F = K/N` and a `Q[F]`-module `M`, `dim_F M = dim_Q M / |F|`, and
`rk_F(A)` is the normalized rank of `A mod N`. A *residual chain* is a nested sequence of
finite-index normal subgroups `N_i` with trivial intersection; `F_i = K/N_i`.
`χ_Q(K) = 1 − b_1(K) + b_2(K)` with `b_k = dim_Q H_k(−; Q)`. `P` is the relation module of an
`n`-generator presentation.

1. **Finite-quotient Swan for big projectives.** For every group `K`, every `C` with
   `r(C) < ∞` and every finite quotient `F = K/N`,

   > `Q[F] ⊗ C ≅ Q[F]^{r(C)}`, hence `rank_Q(Q ⊗_{Z[H]} C) = [K:H] r(C)` for every finite-index `H`.

   No amenability, torsion-freeness or bound on `d(C)` is needed.
2. **Weak Bass is an approximation statement over residually finite groups.** Let `K` be
   residually finite with a residual chain `(N_i)`, and `r(C) < ∞`.
   - (a) *Reverse inequality:* `d(C) <= r(C)`. So `d(C)` is automatically finite and
     `D(C) ∈ [0, r(C)]`.
   - (b) *Interchange formula:* `rk_{F_i}(A_m) <= r(C)` for all `i, m`,
     `sup_m rk_{F_i}(A_m) = r(C)` for every `i`, and

     > `D(C) = lim_i sup_m rk_{F_i}(A_m) − sup_m lim_i rk_{F_i}(A_m)`.

   - (c) Hence the following are equivalent: WBB for `C` (`D(C) <= 0`); `D(C) = 0`;
     *Lück approximation for `C`*, i.e. `lim_i dim_{F_i}(Q[F_i] ⊗ C) = d(C)`; *uniform
     generation*, i.e. for every `δ > 0` there is a finitely generated submodule `M ≤ C` with
     `lim_i dim_{F_i} im(Q[F_i] ⊗ M → Q[F_i] ⊗ C) >= r(C) − δ`.
3. **Euler characteristics of cd-2 groups are multiplicative without finite presentability.** Let
   `K` be finitely generated with `cd_Z K <= 2` and `b_2(K) < ∞`. For every subgroup `H` of finite
   index, `b_2(H) < ∞` and

   > `χ_Q(H) = [K:H] χ_Q(K)`, and `D(res_H P) = [K:H] D(P)` whenever `d(P) < ∞`.

   If `b_1(K) = 0`, then `b_2(H) = [K:H](1 + b_2(K)) − 1 + b_1(H) >= [K:H] − 1`.
4. **Bass defect = degree-2 approximation defect.** Let `K` be infinite, finitely generated,
   residually finite and amenable, with `cd_Z K <= 2` and `b_2(K) < ∞`. Along every residual
   chain, `b_1(N_i)/[K:N_i] → 0` and

   > `lim_i b_2(N_i)/[K:N_i] − b_2^{(2)}(K) = χ_Q(K) = D(P) >= 0.`

   In particular `b_1(K) <= 1 + b_2(K)` for every such `K`.
5. **Reduction, both directions.** The following are equivalent.
   - (a) Kropholler's question for residually finite groups of cd at most 2: every residually
     finite amenable group of `cd_Z <= 2` is elementary amenable.
   - (b) *Lück approximation in degree 2:* every finitely generated residually finite amenable
     group `K` of cd 2 has `b_2(N_i) = o([K:N_i])` along some (equivalently every) residual chain.
   - (c) `l2-finite-projectives-over-amenable-groups-satisfy-weak-bass` for relation modules of
     finitely generated residually finite amenable groups of cd 2.

   A residually finite counterexample `K` with finite abelianization (it exists by item 3(i) of
   `amenable-cd-two-kropholler-iff-locally-indicable` if (a) fails) has
   `b_2(N) >= [K:N] − 1` for every finite-index `N`, and `b_2(N_i)/[K:N_i] → 1 + b_2(K) >= 1`,
   while `b_2^{(2)}(K) = 0`.
6. **Obstruction: an L²-Swan step through an infinite amenable quotient moves the defect and
   does not remove it.** Let `K` be finitely generated with `cd_Z K <= 2` and
   `b_2(K) < ∞`, `N ⊴ K`, `Γ = K/N` infinite, and `P_Γ = Z[Γ] ⊗ P`. Write `β_k = dim_{U(Γ)} H_k(K; U(Γ))` and
   `χ^{(2)}(K; Γ) = β_0 − β_1 + β_2` (assume `β_2 < ∞`). Then

   > `D_Γ(P_Γ) = χ_Q(K) − χ^{(2)}(K; Γ)` and, if `K` is amenable, `D_K(P) = D_Γ(P_Γ) + χ^{(2)}(K; Γ)`.

   - (a) The L²-Swan statement for `(K, N, P)` is literally weak Bass for `P_Γ` over `Γ`, i.e.
     `χ^{(2)}(K; Γ) >= χ_Q(K)`. For finite `Γ` it holds with equality (item 1); for `Γ = K` it is
     the target.
   - (b) To pass from `Γ` to `K` one needs `dim_{U(Γ)}(U(Γ) ⊗ P) <= dim_U(U ⊗ P)`, i.e.
     `χ^{(2)}(K; Γ) <= 0`. In an amenable counterexample (`χ_Q(K) >= 1`) the L²-Swan statement
     and this lifting inequality cannot both hold for any `Γ`, since together they give
     `D_K(P) <= 0`.
     So L²-Swan, even proved for all infinite amenable quotients, does not give the target. The
     missing piece is `L²`-approximation of `χ^{(2)}` from `Γ`-covers to `K`, the analogue of
     item 5(b).
   - (c) The lifting inequality is false for finitely presented modules: `K = Z²`, `N = Z × 0`,
     `M = Z[K]/Z[K](x − 1)` has `dim_{U(K)} = 0 < 1 = dim_{U(Γ)}`. So it must use projectivity.
   - (d) If `b_1(K) = 0` and `Γ` is locally indicable, then `Γ = 1`. The quotients reachable by
     `flat-weak-bass-holds-exactly-for-locally-indicable-groups` are virtually locally indicable
     with finite abelianization.

**Calibrations.**

- *`Z²`, `BS(1,m)`, free groups, surface groups:* `χ_Q` is multiplicative, and `D(P) = 0` for
  the amenable ones. Consistent with items 3–4.
- *Flat modules violate item 2(a).* Over `K = Z = ⟨t⟩`,
  `M = colim(Z[K] →·(t−1) Z[K] →·(t−1) ⋯)` is flat with `r(M) = 0` and `d(M) = 1`, so
  `D(M) = −1 < 0`. The Hantzsche–Wendt flat module `M_B` of
  `amenable-cd-two-bass-defect-equals-euler-characteristic` has `D = +1` and violates item 1:
  `Q[F] ⊗ M_B` is not `Q[F]`-free. So both signs of the defect occur for flat modules over
  residually finite groups. Items 1 and 2(a) use projectivity (Bass + Swan): over a residually finite
  group projectivity already pins `D` to `[0, r]`.
- *Finitely generated `C`* (e.g. `P` for `K` of type `FP_2`): `E` can be taken finite, so
  `A_m = E` for large `m`, the two limits in item 2(b) commute, and `D(C) = 0`. This is the
  weak Bass conjecture for finitely generated projectives over residually finite groups, a known
  case, recovered here from Swan + Lück.

**What this changes.** Over residually finite groups the target inequality has no content beyond
Lück approximation: `D(C) >= 0` always, and `D(C) = 0` is exactly uniform approximation for
`C`. For Kropholler's question the residually finite case is now one named statement: the
normalized second Betti numbers of a residual chain of a finitely generated amenable group of cd 2
tend to `b_2^{(2)} = 0` (known for type `FP_2`, open without it). A residually finite
counterexample must have linear growth of `b_2`, with slope exactly `1 + b_2(K)`. The proposed
L²-Swan route through infinite amenable quotients cannot close the gap by itself (item 6).
