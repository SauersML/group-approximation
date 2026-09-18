---
rg: 2
id: tbar-embeds-in-laurent-leavitt-unit-group-proof
kind: route
title: The winding number of a lift is a locally constant Z-label on the cones of the Thompson element, and labels add along composition
target: tbar-embeds-in-laurent-leavitt-unit-group
requires: []
---

Notation as in the claim.

1. **The labels are locally constant.** For `h in T`, refine the subdivision so that `0` and `h^(-1)(0)` are
   subdivision points. Then no image interval `h(I_(β_i))` wraps past `0`, and on the half-open interval
   `I_(β_i)` the lift `h̃` is affine with `⌊h̃⌋` constant `= n_i`. So `h̃ = h + n_h` with `n_h` constant on each
   `I_(β_i)`.
2. **Well defined.** Refining `(α_i, β_i)` to `(α_i j, β_i j)`, `j = 0,1`, keeps the labels, and
   `s_α t^n t_β = Σ_j s_(αj) t^n t_(βj)` because `t` is central and `Σ_j s_j t_j = 1`.
3. **Cocycle.** For `x in [0,1)`, `h̃(k̃(x)) = h̃(k(x) + n_k(x)) = h(k(x)) + n_h(k(x)) + n_k(x)`, and `h(k(x))` is
   the fractional part. So `n_(h̃k̃) = n_(h̃) ∘ k + n_(k̃)`.
4. **Homomorphism.** After a common refinement with `β_i(h) = α_i(k)`,
   `(s_α t^m t_β)(s_β t^n t_δ) = s_α t^(m+n) t_δ` and the other products vanish. By step 3 this is
   `Ψ(h̃k̃) = Ψ(h̃)Ψ(k̃)`. So `Ψ(h̃^(-1)) = Ψ(h̃)^(-1)` and the image consists of units.
5. **Injective.** The coefficient of `t^n` in `Ψ(h̃)` is `Σ_(i: n_i = n) s_(α_i) t_(β_i)`, a sum of monomials
   with disjoint supports in the basis of `L`. So `Ψ(h̃)` determines the code pairs of `h` and every label,
   hence `h̃`. The translation `x -> x+1` has `h = id` and `n ≡ 1`, so it maps to `t`.
6. **Rotations.** The lift of rotation by `2^(-m)` has label `0` on `I_(w_j)` for `j < 2^m − 1` and label `1` on
   the last interval, which gives the displayed `r_m`. Squaring doubles the rotation angle, so `r_(m+1)^2 = r_m`.
7. **`(Q,+)`.** This is Belk--Hyde--Matucci's theorem that `T̄ >= (Q,+)`, as cited in the claim. ∎
