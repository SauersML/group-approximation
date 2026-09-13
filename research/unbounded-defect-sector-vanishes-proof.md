---
rg: 2
id: unbounded-defect-sector-vanishes-proof
kind: route
title: Gram densities of kernel intertwiners have pointwise rank at most dim rho, so the block algebra has multiplicity at most dim rho, its commutant is finite, and conjugate nested projections coincide
target: unbounded-defect-sector-vanishes-in-koopman-models
requires:
  - kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient
  - kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure
  - bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect
artifacts:
  - research/artifacts/rnorm-fibrewise-defect-2026-09-12.md
---

The complete proof is below. Artifact Sections 1–4 repeat it with context.

**Inputs.**
- `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`: `A = D^N = D^G`,
  so `A` commutes with `sigma(G)`.
- `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`:
  - `H_rho = V_rho (x) W_rho`;
  - `sigma(g)|_(H_rho) = U_rho(g) (x) W_rho(g)`, with `U_rho(g)` in the strong
    closure of `T . rho(N)`;
  - `A|_(H_rho) = 1 (x) A_rho`;
  - item 4: bounded multiplicity forces `W_rho(g)` to be scalar.
- `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`: the sectors
  `H_b`, `H_wm` and `H_inf`, and items 1–4 on `H_b`.

**Step 1 (Gram densities).** Let `N` act on `(Y, mu)` by measure-algebra
automorphisms, with `A = L^inf(Y)^N`. Let `rho` be irreducible with orthonormal
basis `e_1, ..., e_d`. For `T, S in W_rho` put
`g_(T,S) = sum_k (T e_k) . conj(S e_k)`, which lies in `L^1(Y)`.
1. **Invariance.** Koopman operators are multiplicative and commute with
   conjugation. For the row `F_T = (T e_1, ..., T e_d)`, `pi(n) F_T = F_T rho(n)`.
   So `pi(n) g_(T,S) = F_T rho(n) rho(n)^* F_S^* = g_(T,S)`.
2. **Density.** By Schur, `S^* T = c . 1` with `c = <T, S>_W = (1/d) int g_(T,S)`.
   For `a in A`, `aT` lies in `W_rho` and `g_(aT,S) = a g_(T,S)`. So
   `<aT, S>_W = (1/d) int a g_(T,S)`. An invariant `L^1` function is determined by
   its integrals against `A`.
3. **Rank.** Pointwise, `[g_(T_i,T_j)(y)]` is the Gram matrix of the vectors
   `F_(T_i)(y)` in `C^d`. For `d+1` intertwiners its determinant vanishes almost
   everywhere.

**Step 2 (multiplicity at most `d`).**
1. Let `xi_0, ..., xi_d in W_rho` satisfy `<a xi_i, xi_j> = delta_ij <a xi_0, xi_0>`
   for all `a in A`.
   - By Step 1.2, `g_(xi_i,xi_j) = delta_ij g_(xi_0,xi_0)` almost everywhere.
   - By Step 1.3, `g_(xi_0,xi_0)^(d+1) = 0` almost everywhere.
   - So `||xi_0||^2 = (1/d) int g_(xi_0,xi_0) = 0`.
2. Suppose `A_rho'` had a homogeneous summand of degree at least `d+1`.
   - Choose orthogonal equivalent abelian projections `p_0, ..., p_d` in that
     summand, partial isometries `v_i in A_rho'` from `p_0` to `p_i`, a nonzero
     `xi in p_0 W_rho`, and `xi_i = v_i xi`.
   - `A_rho` is central in `A_rho'`, so
     `<a xi_i, xi_j> = <a v_j^* v_i xi, xi> = delta_ij <a xi, xi>`.
   - This contradicts part 1.
3. So `A_rho'` is type I with every degree at most `d`, hence finite.

**Step 3 (nested conjugates).** Let `V` and `P` commute with `A_rho`, with
`V^* P V <= P`.
1. `P_k = V^(*k) P V^k` decreases, so the differences
   `Q_k = P_k - P_(k+1) = V^(*k) Q V^k` are pairwise orthogonal and commute with
   `A_rho`.
2. For `xi in Q W_rho`, the vectors `xi_k = V^(*k) xi` lie in `Q_k W_rho`.
   - `<a xi_i, xi_j> = 0` for `i != j`.
   - `<a xi_k, xi_k> = <V^k a V^(*k) xi, xi> = <a xi, xi>`.
3. Step 2 gives `xi = 0`. If instead `P <= V^* P V`, apply this to `V^*`.

**Step 4 (the cover).**
1. **Multiplicity.** `sigma(N)` acts on the Loeb measure algebra of `X_U`. `D_U` is
   the tracial ultraproduct of the diagonals, which is `L^inf(X_U, mu_U)` because
   every Loeb set agrees almost everywhere with an internal set. So `D^N` is weakly
   closed, and `A = D^N` is `L^inf` of the invariant sigma-algebra. By Step 2, `A_rho` has
   multiplicity at most `dim rho` on all of `W_rho`. `W_rho` is invariant under
   `A_rho` and `W_rho(G)`, so every `H_rho` lies in `H_b`. Hence `H_inf = 0` and
   `H_b = H (-) H_wm`.
2. **`Q = 0`.** `A` commutes with `sigma(u)`, and `U_rho(u) != 0`, so `A_rho`
   commutes with `W_rho(u)`. Likewise each `W_rho(gamma)` commutes with `A_rho`,
   so its fixed space reduces `A_rho` and `P` commutes with `A_rho`. Step 3 with
   `V = W_rho(u)` gives `P' = P`, so `Ind(E_P) = 1`.
3. **Scalars.** Apply item 4 of the isotypic claim with `E = W_rho` and
   `m = dim rho`: `W_rho(g)` is scalar. Item 3 there then puts `sigma(g)|_(H_rho)`
   in the strong closure of `T . sigma(N)|_(H_rho)`.
4. **Invariant subspaces.**
   - Let `K` be a closed `sigma(N)`-invariant subspace of `H (-) H_wm`. Its
     projection lies in `sigma(N)'`, and each `P_rho` lies in `sigma(N)''`. So they
     commute, and `K` is the closed sum of the spaces `P_rho K`. By part 3 each of
     these is `sigma(G)`-invariant.
   - A finite-dimensional `sigma(Gamma_hat)`-invariant subspace is
     `sigma(N)`-invariant, so it lies in `H (-) H_wm`.
5. **Blindness.** Items 1–4 of the bounded-multiplicity claim were proved for `H_b`,
   and part 1 identifies `H_b` with `H (-) H_wm`. ∎
