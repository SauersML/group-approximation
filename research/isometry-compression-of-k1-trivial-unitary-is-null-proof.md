---
rg: 2
id: isometry-compression-of-k1-trivial-unitary-is-null-proof
kind: route
title: Conjugate diag(u,1) into diag(C_S(u),1), then fold a stable null-homotopy back into A with isometries under the defect
target: isometry-compression-of-k1-trivial-unitary-is-null
requires: []
---

Throughout, `≲` is Murray--von Neumann subequivalence of projections.

**Item 1.** Put `P = 1 − SS^*` and `W = [[S, P], [0, S^*]] ∈ M_2(A)`. Using `S^*S = 1`, `PS = 0` and
`S^*P = 0`, both `WW^*` and `W^*W` equal 1, and `W diag(u, 1) W^* = diag(SuS^* + P, 1) = diag(C_S(u), 1)`.
Unitary conjugation does not change `K_1`-classes, so `[C_S(u)] = [u]`.

**General statement.** Let `q = 1 − p` be properly infinite and full, `v ∈ U(pAp)`, `w = v + q`,
`[w] = 0`.
- Since `[w] = 0`, there are `n ≥ 1` and a path `z_t` in `U_{n+1}(A)` from `diag(w, 1_n)` to `1_{n+1}`.
- A properly infinite full projection `q` satisfies `1 ≲ q`. Fullness gives `1 ≲ q ⊗ 1_m` for some
  `m`, and proper infiniteness gives `q ⊗ 1_m ≲ q`.
- Proper infiniteness gives orthogonal projections `g_1, g_2 ≤ q` with `g_1 ~ q ~ g_2`. Then `g_2`
  is properly infinite and full, so by iterated halving it contains `n` mutually orthogonal
  projections, each equivalent to `g_2` and hence `≳ 1`.
- Choose a partial isometry `V` with `V^*V = q` and `VV^* = g_1`. Choose isometries `T_1, …, T_n`
  (`T_i^*T_i = 1`) whose range projections are mutually orthogonal and lie below `g_2`.
- Put `T_0 = p + V`. From `V = Vq` and `VV^* ≤ q` we get `Vp = 0` and `pV = 0`. So `T_0^*T_0 = p + q = 1`
  and `T_0T_0^* = p + g_1`. The ranges of `T_0, T_1, …, T_n` are mutually orthogonal. Put
  `Q = Σ_{i=0}^n T_iT_i^*`.
- For `z = (z_ij) ∈ U_{n+1}(A)` put `Φ(z) = Σ_{i,j} T_i z_ij T_j^* + (1 − Q)`. Since `T_j^*T_k = δ_jk`,
  Φ is a continuous map into `U(A)` with `Φ(1_{n+1}) = 1`.
- `T_0 w = (p + V)(v + q) = v + V`, because `v = pv` and `Vv = Vpv = 0`. So
  `T_0 w T_0^* = (v + V)(p + V^*) = v + g_1`, using `vp = v`, `pV^* = 0`, `Vp = 0`. Hence
  `Φ(diag(w, 1_n)) = v + g_1 + Σ_{i≥1} T_iT_i^* + 1 − Q = v + (1 − p) = w`.
- `t ↦ Φ(z_t)` is a path in `U(A)` from `w` to 1. Square.

**Item 2.** Apply the general statement with `p = SS^*` and `v = SuS^* ∈ U(pAp)`; item 1 gives
`[w] = [u] = 0`.

**Item 3.** If `A` is K1-injective, `u ~_h 1 ~_h C_S(u)` by item 2. Conversely, if `u ~_h C_S(u)` then
`u ∈ U_0(A)` by item 2.

**Model tests.**
- `A = B(H)`, `S` the unilateral shift of infinite multiplicity: `K_1 = 0` and `U(B(H))` is connected,
  so the conclusion is consistent.
- `A = O_2`, `S = s_1`: the defect `s_2s_2^*` is properly infinite and full, `K_1(O_2) = 0`, and
  `U(O_2)` is connected. Consistent again.
- The proof uses the hypothesis on `1 − SS^*` only to fit `n` copies of 1 under the defect. It is not
  claimed to be necessary.

**Credit.** The general statement is the step that Blanchard--Rohde--Rørdam, arXiv:0704.1554v1, cite as
"[13, Exercise 8.11]" at the end of their proof of Lemma 2.4(ii). The argument above is self-contained,
and the exercise text was not read. Nothing here is claimed as new beyond the isometry form and its use
in `defect-ideal-connected-iff-one-isometry-unit-axiom`.
