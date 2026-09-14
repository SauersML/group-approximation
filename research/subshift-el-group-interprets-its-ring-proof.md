---
rg: 2
id: subshift-el-group-interprets-its-ring-proof
kind: route
title: The centre of the crossed product is F_2, so commuting with e_12(s) and e_23(s) for a ring-generating set S forces an element to be e_13(r); commutators of Weyl conjugates then give the multiplication
target: subshift-el-group-interprets-its-crossed-product-ring
requires: []
artifacts:
  - research/artifacts/sk-first-order-plan-2026-09-14.md
---

Full proof in the artifact, §§1–4. Self-contained: no import beyond the definitions.

- **Lemma Z, `Z(R) = F_2`.** Write `z = Σ_j f_j u^j`. From `zu = uz`, `f_j = f_j∘T^{-1}`, so each `f_j` is a `T`-invariant clopen function and hence constant by minimality, say `c_j ∈ F_2`. From `zf = fz` for `f ∈ LC(X,F_2)`, `c_j(f∘T^{-j}) = c_j f` for every `f`, so `c_j ≠ 0` forces `T^j = id`. `X` infinite and minimal makes `T` aperiodic, so `c_j = 0` for `j ≠ 0`.
- **Lemma C, the centraliser.** `g ∈ GL_3(R)` commutes with `e_12(r)` iff `g·rE_12 = rE_12·g`, which reads `g_{i1}r = 0` for `i ≠ 1`, `r g_{2j} = 0` for `j ≠ 2`, and `g_{11}r = r g_{22}`.
  - At `r = 1`: `g_{21} = g_{31} = g_{23} = 0` and `g_{11} = g_{22}`.
  - From `e_23(1)`: `g_{12} = g_{32} = 0` and `g_{22} = g_{33}`.
  - So `g = cI + g_{13}E_{13}`, and the conditions at general `s ∈ S` say `cs = sc`. As `S` generates `R` as a unital ring, `c ∈ Z(R) = F_2`, and invertibility gives `c = 1`.
  - Conversely `E_13E_12 = E_12E_13 = E_13E_23 = E_23E_13 = 0`, so `U_13` centralises `U_12 ∪ U_23`.
- **Lemma W, permutations.** In characteristic 2, `[[1,1],[0,1]]·[[1,0],[1,1]]·[[1,1],[0,1]] = [[0,1],[1,0]]`, so `P_23 = e_23(1)e_32(1)e_23(1) ∈ G` and `P_12 = e_12(1)e_21(1)e_12(1) ∈ G`. Conjugation by `P_σ` sends `e_ij(r)` to `e_{σ(i)σ(j)}(r)`, so every root subgroup is `G`-conjugate to `U_13` by an explicit parameter.
- **Interpretation.** Domain `U_13` with `e_13(r) ↔ r`; addition is the group law; `0` is the identity and `1` is the parameter `e_13(1)`; multiplication is `[w_{12}aw_{12}^{-1}, w_{23}bw_{23}^{-1}]`, which equals `e_13(rs)` by the commutator relation `[e_12(r),e_23(s)] = e_13(rs)`.

**Model test.** For a periodic orbit of period `p`, `u^p` is central, Lemma Z fails exactly at aperiodicity, and the centraliser above is strictly larger than `U_13`.
