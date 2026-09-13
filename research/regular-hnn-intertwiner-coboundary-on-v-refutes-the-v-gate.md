---
rg: 2
id: regular-hnn-intertwiner-coboundary-on-v-refutes-the-v-gate
kind: claim
title: A trivialization of the regular HNN intertwiner cocycle on Thompson's V makes V F_3-linear sofic and refutes the V gate
distinct_from:
  level-unit-hnn-extensions-have-anti-central-rank-models: that builds single-letter partial conjugations of the level unit group, one letter at a time; this is about coherence of all letters of V at once, the commutant-valued cocycle those single-letter intertwiners leave.
  thompson-v-carries-ternary-nonaugmentation-rank-function: that asks for any non-augmentation rank function on F_3[V]; this says a coboundary for the regular intertwiner cocycle would give one, together with an F_3-linear sofic approximation compatible with the regular level model.
  v-detecting-rank-functions-extend-to-ternary-leavitt-units: that is the transfer from V to the unit group; this shows the natural candidate transfer already decides the V gate on V alone.
artifacts:
  - research/artifacts/hnn-intertwiner-cocycle-on-thompson-v-2026-09-12.md
  - research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md
---

**OPEN** (proof: Sections 2–3 of the first linked artifact; held open pending re-derivation by `w3-vf-linear`).

**Setting.**
- `G_3 = L_(F_3)(1,2)^x`, `z = −1`, and `L` is the level unit group.
- `σ_reg` is the regular anti-central model of `L` in the rank ultraproduct `M`.
- For `v ∈ V`, `B_v` is the group of level units that are block diagonal for the length-change partition of `v`, and
  `X_v ∈ M^x` intertwines `σ_reg` with `φ_v = Ad(v)` on `B_v` (Theorem 2.3 of the second artifact).
- `c(u,v) = X_(uv)^(−1) X_u X_v` lies in the commutant of `σ_reg(B_(u,v))` and satisfies
  `c(u, vw) c(v, w) = c(uv, w) · Ad(X_w^(−1))(c(u, v))`.

**Statement.**
1. **Barrier.** Suppose some intertwiners `Y_v = X_v m_v`, with `m_v ∈ σ_reg(B_v)'`, form a homomorphism
   `V -> M^x`. Then that homomorphism is injective. So `F_3[V]` carries a detecting Sylvester rank function,
   `thompson-v-ternary-rank-functions-are-augmentation` is false, and `V` is `F_3`-linear sofic.
2. **Converse.** If the V gate holds, the cocycle class is nontrivial. Deciding the class by relator checks is
   therefore at least as hard as the V gate.
3. **Descent.** Suppose the trivialization agrees with `σ_reg` on `V ∩ L` and kills the kernel of
   `(L ∗_(V∩L) V)/⟨⟨v a v^(−1) = φ_v(a)⟩⟩ -> G_3`. Then:
   - it is an injective model `G_3 -> M^x` with `rk(1 − [z]) = 1`;
   - `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` is false, and so is
     `ternary-anti-central-summand-has-no-weakly-finite-image`;
   - the image of `S_−` is a nonzero stably finite ring (first alternative of Proposition 5.2 of
     `research/artifacts/v-rank-extension-to-ternary-leavitt-units-2026-09-12.md`).

**Proof idea.** If the kernel of `ρ_V` were all of the simple group `V`, conjugation by `ρ_V(v)` would fix
`σ_reg(τ_[0])` while mapping it to `σ_reg(τ_(v[0]))`. That contradicts injectivity of `σ_reg` on `L`.

## Attempts

- 2026-09-12 `w7-hnn-cocycle` (first artifact, Section 4).
  - **Trivial so far.** The class is trivial on level permutations, involutions, the invariant-domain three-cycle
    `C : 0 -> 11 -> 10 -> 0`, and one square-root case.
  - **First undecided relators.**
    - An order-3 element with non-invariant domain. Its group `⟨B_g, g⟩` is not locally finite, since its span
      contains `s_11 s_0 t_11`.
    - Commutation of two disjointly supported depth-changing involutions.
  - **Where it stops.** No decision.
