---
rg: 2
id: subshift-el3-parabolic-subgroups-are-maximal-proof
kind: route
title: Support alignment, a commutator in a tower copy of GL_d(F_2), Grassmann maximality, and a level-ideal covering
target: subshift-el3-parabolic-subgroups-are-maximal
requires: []
artifacts:
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part1.md
---

Complete proof: artifact §3. Outline for `P`; `P′` is symmetric. Let `P < H ≤ G` and `g ∈ H ∖ P`.

**1. Indices.** Pick `i, l ∈ {2,3}` with `g_{i1} ≠ 0` and `(g^{−1})_{l1} ≠ 0`.

**2. Alignment.**
- Multiply on the right by `diag(1, u^{∓s}, u^{±s}) ∈ P` (Whitehead in characteristic 2). This shifts the support set of `(g^{−1})_{l1}` by `T^s`.
- By minimality, the supports of `g_{i1}` (read through `T^{−a}` on the `u^a` coefficients) and of `(g′^{−1})_{l1}` meet in a nonempty clopen set.

**3. Finite group.**
- Take a small clopen `V` inside that set, with `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w` and all coefficients constant on the `T^aV`.
- `ε_ab = e_{T^aV}u^{a−b}` (`|a|,|b| ≤ w`) give `S = ι(GL_{3(2w+1)}(F_2)) ⊆ G`.
- `h = e_{1l}(e_V) ∈ P ∩ S`. By the product formula `f u^a e_V f′ u^b = f|_{T^aV} f′|_V ε_{a,−b}`, the commutator `k = g′ h g′^{−1} h^{−1}` lies in `H ∩ S`.
- `k_{i1} = g′_{i1} e_V (g′^{−1})_{l1} ≠ 0`, so `k ∉ P`.

**4. Grassmann maximality** (proved in the artifact).
- In `GL_n(F_2)` the stabilizer `Q` of an `m`-subspace `U` is maximal.
- An overgroup's orbit of `U` contains a sphere `S_t(U)` of the Grassmann graph, and then `S_1(U)` by explicit subspace choices. The Grassmann graph is connected, so the orbit is everything, and counting gives the whole group.
- `S ∩ P = ι(Q)` for `U = F_2^{2w+1} ⊗ e_1`, so `H ∩ S = S` and `e_21(e_V) ∈ H`.

**5. Level ideal.** `J = {r : e_21(r) ∈ H}` is additive.
- `[e_32(t), e_21(r)] = e_31(tr)` and `[e_23(t), e_31(r)] = e_21(tr)` give `RJ ⊆ J`.
- Conjugation by `diag(v, v^{−1}, 1) ∈ P` gives `Jv ⊆ J` for units `v`.
- So `e_{T^jV} = u^j e_V u^{−j} ∈ J`, `J` is closed under unions of clopen idempotents, and minimality gives `1 ∈ J`.
- Then `H ∋ e_21(R), e_31(R)`, and together with `P ∋ e_12, e_13, e_23, e_32` this gives `H = G`. ∎
