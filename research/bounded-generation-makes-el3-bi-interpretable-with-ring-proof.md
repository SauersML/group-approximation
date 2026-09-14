---
rg: 2
id: bounded-generation-makes-el3-bi-interpretable-with-ring-proof
kind: route
title: Commuting with two neighbouring root subgroups leaves a central unit plus a corner entry, and a fixed-length factorisation into elementary matrices reads the matrix of a group element off the interpreted ring
target: bounded-generation-makes-el3-bi-interpretable-with-ring
requires: []
artifacts:
  - research/artifacts/sk-first-order-plan-2026-09-14.md
---

Full computation in the artifact §§2–5, written there for the subshift crossed product; only the two displayed hypotheses are used.

**Part 1, the ring in the group.** For `g ∈ GL_3(R)`, commuting with `e_12(r)` says `g·rE_12 = rE_12·g`, that is `g_{i1}r = 0` for `i ≠ 1`, `rg_{2j} = 0` for `j ≠ 2`, and `g_{11}r = rg_{22}`.
- At `r = 1`: `g_{21} = g_{31} = g_{23} = 0` and `g_{11} = g_{22}`. Commuting with `e_23(1)` gives `g_{12} = g_{32} = 0` and `g_{22} = g_{33}`.
- So `g = cI + g_{13}E_{13}`, and `(cI + aE_{13})(c'I + a'E_{13}) = cc'I + (ca' + c'a)E_{13}`, so `c` is a central unit, hence `1` by hypothesis.
- The conditions for general `s ∈ S` say `cs = sc`; with `S` generating `R` this is what makes `c` central.
- Conversely `E_{13}E_{12} = E_{12}E_{13} = E_{13}E_{23} = E_{23}E_{13} = 0`, so `U_13` centralises `U_12 ∪ U_23`.
- Weyl parameters: the monomial matrices of the coordinate permutations lie in `E_3(R)` (in characteristic 2 already `e_23(1)e_32(1)e_23(1)` is the transposition matrix), and conjugating by them carries `U_13` onto each `U_ij`. Multiplication is then `[e_12(r), e_23(s)] = e_13(rs)`.

**Part 2, the group in the ring.** Interpret `M_3(R)` as `R^9`. A fixed position pattern turns

    G = { M : ∃ r_1 … r_m, M = ê_{i_1j_1}(r_1) ⋯ ê_{i_mj_m}(r_m) }

into an existential formula, so `G` is definable in `R` with no parameters, with the definable matrix product as its group law.

**Part 3, the two composites.**
- Ring side: `r ↦ ê_{13}(r) ↦ r` has definable graph.
- Group side: with `R^*` the interpreted ring and `G^*` the copy of `G` interpreted in `R^*`, set

      Θ(g,M) :⟺ ∃ a_1 … a_m ∈ U_13 [ g = ∏_k w_{i_kj_k} a_k w_{i_kj_k}^{-1} ∧ M = ∏_k ê_{i_kj_k}(a_k) ].

  Total by the bound; single-valued because under `R^* ≅ R` the second product is the matrix `∏_k e_{i_kj_k}(r_k) = g`, so it does not depend on the factorisation; injective because elements of `G` are matrices; surjective and multiplicative by applying the bound in `G^*` and to `gh`. So `Θ` is a definable isomorphism and the pair is bi-interpretable with parameters.

**Model tests.**
- `R = F_2` (or any finite field): the only central unit is `1`, `E_3(F_2) = SL_3(F_2)` is boundedly generated, and the conclusion is the trivial interpretation of a finite ring in a finite group.
- `R` commutative with a central unit `c ≠ 1`, for instance `R = F_3`: then `cI ∈ C_G(U_12 ∪ U_23) ∖ U_13`, and part 1 correctly fails as stated. (For fields one repairs it by passing to `PGL`, which is outside the scope of this claim.)
- `R = Z`, `G = E_3(Z) = SL_3(Z)`: both hypotheses hold, and the conclusion is the known bi-interpretability of `SL_3(Z)` with `Z`.
