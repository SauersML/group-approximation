---
rg: 2
id: lef-iff-subgroup-of-simple-kazhdan-limit-finite-simple-proof
kind: route
title: Configuration-space models of the lamplighter host are onto matrix algebras, so the host is a marked limit of SL_3N(F_2) expanders
target: lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple
requires: [lef-groups-embed-in-simple-kazhdan-lef-groups, lamplighter-bernoulli-crossed-products-simple-kazhdan-lef, elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/sk-strong-6-envelope-table-2026-09-13.md
---

**(2) ⇒ (1).** A marked limit of finite groups is LEF: a finite set of relations and non-relations of `G` holds in
`SL_(3N_k)(F_2)` for large `k`. Subgroups of LEF groups are LEF.

**(1) ⇒ (2).** Take `Δ`, `L`, `R`, `G` as in the claim. Then `G` is infinite, finitely generated, simple and Kazhdan, and
`γ ↦ diag(u_γ,1,1)` embeds `Γ ≤ [Δ,Δ] ≤ [L,L]` in `G` (`lef-groups-embed-in-simple-kazhdan-lef-groups`,
`lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`).

*Generators.*
- Fix a finite symmetric generating set `S` of `Δ`, the flip `a ∈ L`, and `p = 1_[x(e)=1] ∈ LC(Y,F_2)`.
- `R` is generated as a ring by `u_s` (`s ∈ S`), `u_a` and `p`.
- Let `F = F_2⟨t_s, t_a, t_p⟩` be the free algebra and `π: F → R` the surjection.

*Models.*
- Let `φ_n: Δ → Q_n` be LEF models: injective on the `n`-ball and multiplicative on pairs whose product stays in it.
  Replace `Q_n` by `⟨φ_n(S)⟩`. Since `Δ` is infinite, `|Q_n| ≥ |B_n| → ∞`.
- Let `L_n = Z/2 ≀ Q_n` act on `Y_n = 2^(Q_n)` by `(t·y)(h) = y(t^(-1)h)`, with `a` flipping `y(e)`. Extend `φ_n` to a
  partial homomorphism `φ̂_n` on the elements of `L` whose `Δ`-part and flip support lie in the `n`-ball.
- On `V_n = F_2^(Y_n)`, let `P_g` be the permutation matrix of `g ∈ L_n`.
- For `f` depending on coordinates in a finite `W ⊆ B_n`, let `D_n(f)δ_y = f(x_y)δ_y`. Here `x_y` is any point of `Y` with
  `x_y(w) = y(φ_n(w))` for `w ∈ W`; it exists because every configuration is legal and `φ_n` is injective on `W`.
- Put `ψ_n(Σ_ℓ f_ℓ u_ℓ) = Σ_ℓ D_n(f_ℓ) P_(φ̂_n(ℓ))` when all data lie in the `n`-ball.

*(i) Multiplicativity.* For `ℓ` and `f` in a fixed ball, `P_(φ̂_n(ℓ)) D_n(f) P_(φ̂_n(ℓ))^(-1) = D_n(f∘ℓ^(-1))` once `n` is
large: the action of `φ̂_n(ℓ)` on the pattern of `y` over the relevant window matches the action of `ℓ` on `Y`. So for
fixed `r, s ∈ R`, `ψ_n(r+s) = ψ_n(r)+ψ_n(s)` and `ψ_n(rs) = ψ_n(r)ψ_n(s)` for large `n`.

*(ii) Nonvanishing.*
- Let `r = Σ f_ℓ u_ℓ ≠ 0` with `f_(ℓ_0) ≠ 0`, and let `E` be the finite set `{ℓ^(-1)ℓ' : ℓ ≠ ℓ' ∈ supp r}`.
- The action is topologically free, so the open set `ℓ_0^(-1){f_(ℓ_0) = 1}` contains a point `x` moved by every `g ∈ E`.
  Each `g·x ≠ x` is witnessed by one coordinate.
- For large `n` pick `y ∈ Y_n` realizing the pattern of `x` on a window containing all these coordinates and all windows
  of the `f_ℓ` and their translates.
- The points `φ̂_n(ℓ)·y`, `ℓ ∈ supp r`, are distinct. So the column of `ψ_n(r)` at `y` has the entry
  `f_(ℓ_0)(ℓ_0·x) = 1` in row `φ̂_n(ℓ_0)·y`, and `ψ_n(r) ≠ 0`.

*(iii) Onto.*
- Products of the permutation matrices `P_(φ_n(s))` give `P_t` for every `t ∈ Q_n`.
- `P_t D_n(p) P_t^(-1)` is the diagonal indicator of `y(t) = 1`. Products of these and their complements give every
  diagonal matrix unit, since the coordinates `y(t)`, `t ∈ Q_n`, determine `y`.
- Conjugating the flip at `e` gives flips at every `t`. They generate `(Z/2)^(Q_n)`, which acts simply transitively on
  `Y_n`.
- So the generated algebra contains every matrix unit, and `ρ_n: F → M_(N_n)(F_2)`, `ρ_n(t) = ψ_n(π(t))`, is onto,
  where `N_n = 2^|Q_n|`.

*Convergence and expansion.*
- `EL_3(F)` has property (T) (`elementary-groups-over-fg-rings-have-property-t`). `G` and
  `EL_3(M_(N_n)(F_2)) = SL_(3N_n)(F_2)` are quotients of `EL_3(F)` with compatible generators `e_ij(t)`.
- For a word `W` in these generators, the entries of `W − I_3` lie in a finite subset of `F`. By (i),
  `ρ_n(W − I_3) = ψ_n(π(W − I_3))` for large `n`, so by (ii) `W` is trivial in `G` iff it is trivial in
  `SL_(3N_n)(F_2)` for large `n`.
- So the finite simple groups `SL_(3N_n)(F_2)` converge to `G` as marked groups. The uniform Kazhdan constant of
  `EL_3(F)` makes their Cayley graphs a family of expanders.
