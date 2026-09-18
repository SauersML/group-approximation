---
rg: 2
id: deligne-class-survives-on-every-linear-rational-projective-host
kind: claim
title: For n >= 2, no homomorphism Sp_2n(Z) -> GL_N(Z) makes Deligne's class die on the rational Cantorization of S^(N-1); the rational projective route needs a genuinely piecewise embedding
distinct_from:
  deligne-class-survives-on-standard-rational-projective-hosts: that needs a positive-Lebesgue-measure orbit with a symplectic block in its stabilizer, and so covers the standard and 5-dimensional representations; this uses lower-dimensional orbits lying in no rational hyperplane, and covers every representation, including k*std, which that node's Reading wrongly left open.
  deligne-class-dies-on-some-rational-projective-host: that is the open positive question; this removes every embedding that factors through GL_(m+1)(Z), leaving only genuinely piecewise ones.
  groupoid-lifts-of-central-extensions-need-no-invariant-measure: that handles actions with an invariant probability measure, including finite-image ones; this handles the infinite-image linear actions, which have none.
---

**ESTABLISHED** (lane proof, not reviewed). The textbook inputs are the same as for
`deligne-class-survives-on-standard-rational-projective-hosts` (Mackey–Moore induction,
Guichardet–Wigner), plus Margulis superrigidity and the multiplicity-free structure of
`C[G/U]`. None was re-read at source.

## Statement

Let `n ≥ 2`, `Γ = Sp_{2n}(Z)`, and let `j : Γ → GL_N(Z)` be any homomorphism. Then
Deligne's class does not die in `H^2(Γ; C(Ŝ_{N−1}, Z))` for the action through `j`
on the rational Cantorization `Ŝ_{N−1}` of
`closed-mcg-embeds-in-rational-projective-full-group`. So no embedding of
`Sp_{2n}(Z)` into `𝒯_{N−1}` through `GL_N(Z)` carries the shear lift of
`central-extension-shear-lift-into-rational-projective-groups`.

## Proof

**Step 0: reductions.**
- If the class died for `Γ`, it would die for every finite-index `Γ' ≤ Γ`, where it
  is the restriction of the same `G`-class, `G = Sp_{2n}(R)`.
- If `j` has finite image, some `Γ'` acts trivially, and the class survives by
  `groupoid-lifts-of-central-extensions-need-no-invariant-measure`.
- Otherwise, by Margulis superrigidity, `j = ρ` on some `Γ'` for a rational
  representation `ρ` of `Sp_{2n}`. The compact correction has integral image, hence
  is finite; pass to a smaller `Γ'`. `ρ` is defined over `Q`, since `ρ(Γ')` is
  rational and Zariski dense in `ρ(G)`. `Sp_{2n}` is split, so over `Q`,
  `ρ ≅ ⊕_λ V_λ ⊗ Q^{k_λ}` with the `V_λ` absolutely irreducible and pairwise distinct.

**Step 1: every `V_λ` has invariants under a symplectic block.**
- Let `H = Sp(⟨e_n, f_n⟩)`, the long-root `SL_2`. The coordinate ring
  `C[G/U] = ⊕_λ V_λ^*` is a domain, and the product carries `V_λ^* × V_μ^*` into
  `V_{λ+μ}^*`. So `{λ : (V_λ^*)^H ≠ 0}` is a monoid.
- `V_λ^* ≅ V_λ` for `Sp_{2n}`, so it suffices that the monoid contains the
  fundamental weights:
  - `ω_i`, `i < n`: `e_1 ∧ … ∧ e_i ∈ Λ^i_0 = V_{ω_i}` is fixed by `H`.
  - `ω_n`: `y = e_1 ∧ … ∧ e_{n−2} ∧ (e_{n−1}∧f_{n−1} − e_n∧f_n)` is nonzero and
    primitive: the two contractions by `ω` cancel. It is fixed by `H`, which fixes
    `e_n ∧ f_n` and the other vectors.
- So `V_λ^H ≠ 0` for every `λ`, including `λ = 0`.

**Step 2: an orbit in no rational hyperplane.**
- Pick nonzero `x_λ ∈ V_λ^H` and `a_λ ∈ R^{k_λ}` with `Q`-linearly independent
  coordinates. Put `x = Σ_λ x_λ ⊗ a_λ`.
- The `G`-span of `x` projects onto each of the pairwise non-isomorphic irreducibles
  `V_λ ⊗ a_λ`, so it equals `⊕_λ V_λ ⊗ a_λ`.
- A rational form `φ = (φ_{λ,j})` vanishing there satisfies `Σ_j a_{λ,j} φ_{λ,j} = 0`
  with `φ_{λ,j} ∈ V_λ(Q)^*`, so `φ = 0`.
- So the orbit `O = G·[x] ⊂ S^{N−1}` lies in no rational hyperplane. It is a connected
  real-analytic submanifold, so it meets each rational hyperplane in a null set.
- `E = O ∖ ⋃ {rational hyperplanes}` is therefore `Γ'`-invariant and of full measure
  in `O`. Over `E` the fibres of `π : Ŝ_{N−1} → S^{N−1}` are points, and `π^{-1}|_E`
  is Borel (Lusin–Souslin).

**Step 3: contradiction.**
- If `k` trivializes the class on `Γ' ⋉ Ŝ`, then `κ(γ, x) = k(γ̃, π^{-1}x)` is a
  bounded Borel trivialization of `d·ε` on `Γ' × E`.
- The proof of `deligne-class-survives-on-standard-rational-projective-hosts`, run on
  `O = G/Stab[x]`, then kills the restriction of the universal-cover class to
  `Stab[x] ⊇ H`: Mackey–Moore induction, then integration over `Γ'\G`.
- That restriction is nonzero in `H^2_c(H; R)`, since `H ⊂ G` is an isomorphism on
  `π_1`. ∎

## Consequences

- The Gram–Schmidt repair for `k·std` is impossible: no `Γ`-equivariant map, even a
  Borel one, from the good set works, whatever is done at the bad quadric.
  Attempt 2 of `deligne-class-dies-on-some-rational-projective-host` was too
  optimistic.
- A rational projective host for Deligne's lattice needs `Sp_{2n}(Z) ↪ 𝒯_m` acting by
  genuinely piecewise-linear maps, with no linear model even on a finite-index
  subgroup. The same argument applies to any piecewise action that preserves the
  measure class of some orbit lying in no rational hyperplane, with a block in its
  stabilizer (hand remark).
