---
rg: 2
id: finitely-generated-positive-cones-are-discrete-proof
kind: route
title: The first letter of a positive word is a left divisor, so the least generator is least; successor intervals are finite, which turns a Baumslag–Solitar relation into a counting contradiction
target: finitely-generated-positive-cones-are-discrete
requires: []
---

Notation is that of the target. Recall that `x < y` iff `x^{-1} y ∈ P`, and `x ≤ y` iff `x^{-1} y ∈ M`.

**1. Discreteness.**
- Let `g ∈ P` and write `g = s_1 ⋯ s_m` with `s_i ∈ S⁺`. Then `s_1^{-1} g = s_2 ⋯ s_m ∈ M`, so `s_1 ≤ g`.
  Hence `e = min S⁺ ≤ s_1 ≤ g`, and `e` is the least element of `P`.
- **Successors.** `x < y` iff `x^{-1}y ∈ P` iff `x^{-1} y ≥ e` iff `y ≥ xe`. So `xe` is the least element above `x`.
  By induction, `[x, x e^a] = {x e^i : 0 ≤ i ≤ a}`.
- **The right order.** Use the last letter instead: `g s_m^{-1} = s_1 ⋯ s_{m−1} ∈ M`, so `s_m ≤′ g`, and the
  `<′`-least element of `S⁺` is `<′`-least in `P`.

**2. Convexity.** If `1 ≤ g ≤ e^N` with `N ≥ 0`, then `g ∈ [1, e^N] = {e^i}` by 1. Negative `N` is the mirror case.

**3. No BS self-conjugacy.**
- Replacing both sides by their inverses, we may assume `a ≥ 1`. Put `x = g^{-1}` and `c = x^{-1} e x`.
  - From `g^{-1} e^a g = e^b` we get `x e^a = e^b x`.
  - Also `c^b = x^{-1} e^b x = e^a`.
- **If `b ≥ 1`.** Then `c > 1`, since otherwise `c^b ≤ 1 < e^a`.
  - So `x < x c < ⋯ < x c^b = x e^a` is a strictly increasing chain of `b + 1` elements of `[x, x e^a]`.
  - That interval has `a + 1` elements, so `b ≤ a`.
- **If `b ≤ −1`.** Then `c^{|b|} = e^{−a} < 1` forces `c < 1`.
  - So `x < x c^{-1} < ⋯ < x c^{b} = x e^a` is a strictly increasing chain of `|b| + 1` elements.
  - Hence `|b| ≤ a`.
- **Symmetry.** `e^a = g e^b g^{-1}` is a relation of the same form, with the roles of `a` and `b` exchanged and
  `g` replaced by `g^{-1}`. The same argument gives `|a| ≤ |b|`. `∎`

**4. Cone normalizers.**
- If `g^{-1}Pg = P`, then `φ(h) = g^{-1} h g` preserves `<`, since `x < y` iff `x^{-1}y ∈ P` iff
  `φ(x)^{-1}φ(y) ∈ P`. An order automorphism fixes the least positive element, so `g^{-1} e g = e`.
- For a quasi-central `Δ`, `Δ^{-1} S⁺ Δ ⊆ M − {1}`, so `Δ^{-1} P Δ ⊆ P`.
- Two positive cones `Q ⊆ P` are equal. For `p ∈ P − Q`, either `p^{-1} ∈ Q ⊆ P`, which is impossible, or
  `p = 1`, which is also impossible.

**5. Distortion.**
- Let `e^N = t_1 ⋯ t_m` with `t_i ∈ S⁺`. The partial products increase from `1` to `e^N`, so they lie in
  `[1, e^N] = {e^i}` by 1.
- Each `t_i` is then a quotient of two powers of `e`, hence a power `e^k ∈ S⁺` with `1 ≤ k ≤ K_e`. So `m ≥ N/K_e`.
- If `|e^N| ≤ n`, then the element `e^N` has `S`-length at most `n` and `ℓ_+ ≥ N/K_e`. So
  `D_P(n) ≥ Dist_e(n)/K_e`. `∎`
