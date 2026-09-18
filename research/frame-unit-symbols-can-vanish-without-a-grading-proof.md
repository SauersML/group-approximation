---
rg: 2
id: frame-unit-symbols-can-vanish-without-a-grading-proof
kind: route
title: Double the ring lamplighter along the reflection, so the frame unit becomes diag(u, u^-1) and its symbols cancel
target: frame-unit-symbols-can-vanish-without-a-grading
requires:
  - graded-rings-with-degree-one-units-fail-the-k-budget
  - abc-twisted-laurent-k-theory-fibration
  - laurent-rational-symbols-block-fp-elementary-groups
  - infinitely-generated-symbols-block-fp-elementary-groups
---

**Inputs.**
- Morita invariance: `K_*(M_2(S)) ≅ K_*(S)`, and the diagonal map `S × S -> M_2(S)` induces the sum. Textbook.
- (S1) for the commutative subring `Q[u^(±1)] ⊆ R_1`, where `λ` and `u` commute. Dennis–Stein, LNM 342, p. 249,
  read at the source by this lane. It gives `{λ, u^(-1)} = {λ, u}^(-1)`.
- `abc-twisted-laurent-k-theory-fibration` for `(U_n, σ)`. `U_n` is von Neumann regular, hence regular
  supercoherent.

**Part 1.**
- `τ` permutes the tensor factors and conjugates the shift to its inverse.
- For `θ`, the defining relation `u b u^(-1) = σ(b)` must be respected:
  `θ(u) θ(b) θ(u)^(-1) = u^(-1) τ(b) u = σ^(-1)(τ b) = τ(σ b) = θ(σ b)`.
- So `θ` extends to `R_1`, with inverse defined the same way. `ρ` is a unital ring map, injective on `B`.
- `U^(-1) B' U = ρ(u^(-1) B u) = ρ(B) = B'`.

**Part 2.** By Morita invariance, `ρ_* = id + θ_*` on `K_*(R_1)`. So
`{λ, U} = ρ_*{λ, u} = {λ, u} + {θλ, θu} = {λ, u} + {λ, u^(-1)} = 0`, using (S1) pushed forward from
`Q[u^(±1)]`. ∎

**Part 3.**
- *ABC for `(U_n, σ)`.* `σ_*` is the identity on `K_0(U_n) ⊆ Q`, since it fixes `[1]`. It is also the identity on
  `K_1(U_n)`: a class from a finite block and its shift agree in a larger block, where `det(g ⊗ I) = det(I ⊗ g)`.
  So `1 − σ_* = 0` in degrees 0 and 1, and `K_0(U_n)` and `K_1(U_n)` inject into `K_*(R_1)`.
- *`K_0`.* `[1_R] = ρ_*[1] = 2[1_(R_1)]`, which has infinite order because `K_0(U_n) = Z[1/n]` injects.
- *`K_1`.* `[λ·I_2] = ρ_*[λ] = 2[λ]` in `K_1(R_1) ⊇ K_1(U_n) = colim(Q^x --λ↦λ^n--> Q^x)`. Its kernel is the
  set of `λ` with `λ^2` in the torsion of that colimit, which is `{±1}`. ∎

**Part 4.** This is immediate from items 2–3 and the dichotomy.

**Part 5.**
- `diag(u, 1)` commutes with the scalars `λ I_2`. Under Morita, `{λ, diag(u, 1)}` is the class `{λ, u} ∈ K_2(R_1)`.
- By `laurent-rational-symbols-block-fp-elementary-groups`, item 1, these classes map onto the image of `Q^x` in
  `K_1(U_n)`, which is not finitely generated.
- The symbol lemma (`infinitely-generated-symbols-block-fp-elementary-groups`, part 1), applied to the commuting
  units `λ I_2` and `diag(u,1)` of `R`, gives the failure of finite presentation. ∎
