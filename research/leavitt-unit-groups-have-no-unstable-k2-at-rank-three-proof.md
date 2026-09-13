---
rg: 2
id: leavitt-unit-groups-have-no-unstable-k2-at-rank-three-proof
kind: route
title: Vanishing stable K, Khanh's rank-four comparison pulled back through Voronetsky's refinement, and the permutohedron colimit on the hexagon
target: leavitt-unit-groups-have-no-unstable-k2-at-rank-three
requires:
  - ara-cortinas-leavitt-tensor-k-theory-vanishes
  - leavitt-gl-equals-el-and-perfect-unit-group
  - leavitt-steinberg-map-iso-from-rank-three
  - khanh-acyclicity-and-steinberg-criteria
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
  - steinberg-group-is-glued-over-the-permutohedron
artifacts:
  - research/artifacts/leavitt-unstable-k2-steinberg-reduction-2026-09-12.md
  - research/artifacts/gk-vf-gate-verification-2026-09-12.md
---

Complete proof: artifact Sections 1–5 (Steps 1–4 of Section 2, Section 3, Section 4, Proposition 5.1).

**Notation.** `R = L_(F_p)(1,2)` with `p ∈ {2,3}`, `S_r = St_r(R)`, `G_r = GL_r(R)`, `φ_r : S_r -> G_r`,
`N_r = ker φ_r = K_2(r,R)`, and `j_r : S_r -> S_(r+1)` the standard inclusion.

- **Identification.** The code `{0, 10, 11}` gives `R ≅ R^3` as right modules, so `R^x ≅ GL_3(R)`. `GL_3 = E_3` is
  `leavitt-gl-equals-el-and-perfect-unit-group` for `p = 2`, and part 2 of
  `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` for `p = 3`. That proof takes GE from Menal–Moncasi, not
  from the Steinberg comparison, so the use is not circular.
- **Stable part of point 1.** Ara–Brustenga–Cortiñas Theorem 7.6 for one vertex with two loops has `1 - N^t = -1`,
  which is invertible on every `K_n(k)`. So `K_n(R) = 0` for every `n` (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).
- **Binary `N_3 = 1`.**
  - Step 1. `x_ij(a) = [x_ik(a), x_kj(1)]`, so `S_3` is perfect. `H_2(G_3) = 0` by (KH1), and the five-term sequence
    gives `N_3 = [S_3, N_3]`. Khanh's Lemma 5.2 makes `j_3(N_3)` central in `S_4`, so `j_3(N_3) = 1`.
  - Step 2. Theorem 5.1 at `n = 4` (item 2 of `khanh-acyclicity-and-steinberg-criteria`) gives `N_4 = 1`. Its
    hypotheses are Lemma 5.3, Step 1 and Proposition 4.2.
  - Step 3. `T_3(x) = (x_1, x_2, e*x_3, f*x_3)` and `U_3(x_1, x_2, y, z) = (x_1, x_2, ey + fz)` are inverse. So
    `α_3(A) = T_3 A U_3` is an isomorphism `M_3(R) -> M_4(R)`, and it sends `E_33` to `E_33 + E_44`. Khanh's refinement
    is `D_3 = F_α ∘ St(α_3)`. It is bijective by Voronetsky, Proposition 1 at `n = 4` with `S = {1}`
    (arXiv:2004.08551v2, p. 9: "a surjection for n ≥ 3 and a bijection for n ≥ 4").
  - Step 4. `φ_4 D_3 = α_3 φ_3` holds on generators, and `α_3` is injective. So `N_3 = D_3^(-1)(N_4) = 1`.
- **Ternary `N_3 = 1`.** Part 2 of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` with `B = F_3`. The
  stable part supplies `K_1 = K_2 = 0`. At rank three:
  - Step 1 uses Theorem 3.1(1) with `N = 2`.
  - Step 2 uses the signed comparison, Theorem 2.1 of the host artifact, in place of Theorem 5.1. It has transporters
    `W = X_12(-1) X_21(1) X_12(-1)` and `W_23`, and central correction `z = (W_23 W W_23)(W W_23 W)^(-1)`.
  - Step 3 is unchanged, because Voronetsky's setting has no characteristic hypothesis.
- **Injectivity.** `K_2(3,R) = K_2(R) = 0`, so the stability map is injective.
- **Point 2.** With `N_3 = 1`, (St1)–(St3) present `R^x`. (St1) and (St3) hold in abelian subgroups of order at most
  `p^2`. (St2) holds in `{x_ij(λa) x_jk(μb) x_ik(νab) : λ, μ, ν ∈ F_p}`, a quotient of the Heisenberg group over
  `F_p`, so of order at most `p^3`.
- **Point 3.** `K_2(3,R)` has no nontrivial element, so that option of Remark 3.2 of the firewall artifact is empty.
- **Point 4.** Every Steinberg relation lies in one `U_π`. In the hexagon `123, 213, 231, 321, 312, 132`, each root is
  positive on three consecutive orders, so the adjacent identifications make all of them. (SPG2) of
  `steinberg-group-is-glued-over-the-permutohedron` at `n = 3` gives `S_3 = colim U_π = π_1(Y_hex)/<<t>>`, and
  `S_3 ≅ R^x`.

**Imports** (artifact Section 7).
- Khanh, arXiv:2609.08428v1, unrefereed: (KH1), Lemmas 5.2 and 5.3, Proposition 4.2, and Theorem 5.1 through Brown's
  presentation theorem (JPAA 32, 1984).
- The statement of Voronetsky's Proposition 1 (JPAA 225 (2021) 106547). Its proof was not re-derived.
- For `p = 3`, `khanh-acyclicity-and-steinberg-criteria` through the host theorem.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 34 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
