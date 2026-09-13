---
rg: 2
id: four-transvection-units-have-a-weakly-finite-symbol-image
kind: claim
title: The four-transvection group sits in EL_2 of the ternary Jacobson algebra and contains minus one, its symbol is a weakly finite model sending minus one to minus one, and every five-transvection extension has one too
distinct_from:
  jacobson-elementary-subgroups-are-locally-finite-by-linear: that is the structure of elementary groups over the Jacobson algebra; this identifies the four-transvection group as one of them through the code-(0,1) frame and uses the symbol as an anti-central weakly finite model, with image SL_2(F_3[ζ, ζ^(-1)]).
  depth-monotone-configurations-cannot-force-ternary-minus-one: that firewalls configurations inside weighted unit groups; this firewalls S4 and every five-transvection set, which no conjugation puts inside any of them, by symbol and character models.
artifacts:
  - research/artifacts/four-transvection-escape-set-2026-09-12.md
---

**OPEN** (proved on paper, artifact Sections 2 and 3; held OPEN until `w4-vf-gate` re-derives it).

**Statement.** Let `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `ε_- = 2(1 - [z])`, and
`S4 = {T_(0,1), T_(1,0), T_(1,00), T_(00,1)}` with `T_(σ,κ)(λ) = 1 + λ s_σ t_κ`. Let `Φ(x) = (t_i x s_j)` be the
code-`(0,1)` isomorphism `R -> M_2(R)`, and `T = F_3<s_0, t_0>`, isomorphic to the Jacobson algebra.
1. `Φ(S4) = {E_01(1), E_10(1), E_10(t_0), E_01(s_0)}`, the span of `<S4>` is `Φ^(-1)(M_2(T))`, and `z in <S4>`.
2. The symbol `s_0 -> ζ`, `t_0 -> ζ^(-1)` maps `Φ(<S4>)` onto `SL_2(F_3[ζ, ζ^(-1)])` with `z -> -I`. So
   `ε_- F_3[<S4>]`, and the same algebra for every conjugate, has a nonzero weakly finite image.
3. For every transvection `T = T_(σ,κ)(λ)`, the span of `<S4, T>` has a unital homomorphism into `M_2(F_3)`. It comes
   from the action of `R` on the sequences that are eventually `0`, and it sends `z` to `-I`.
4. `x_12(1) = 1 + s_0 t_10` lies in `<S4>`, and `x_23(1) = 1 + s_10 t_11` does not. No code frame of `{0, 10, 11}` or
   `{1, 00, 01}` has both roots in `<S4>`.
5. For `S6 = S4 ∪ {T_(01,1), T_(1,01)}` the span is all of `R`, which has no nonzero weakly finite algebra image.

**Consequences.**
- `S4` is not the candidate input for `ternary-anti-central-summand-has-no-weakly-finite-image`. No derivation inside
  `ε_- F_3[<S4, T>]`, or inside a conjugate, can reach an obstruction.
- `<S4>` is not amenable: its image `SL_2(F_3[ζ, ζ^(-1)])` is finitely generated, linear and not virtually solvable,
  so it contains a free group by the Tits alternative.
- An anti-central model that is not an algebra homomorphism needs at least six transvections, or a relation outside
  the span of the group.

**Scope.** Soficity, LEF and residual finiteness of `<S4>` are not decided. The defect form on `<S4, x_23(1)>` is
`four-transvections-and-x23-force-defect-vanishing`. Conjugate frames inside `<S4>` are not classified.
