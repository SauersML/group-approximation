---
rg: 2
id: fw-shell-inputs-at-window-zero-are-highly-transitive-proof
kind: route
title: Transfix the graph of the shift, read orbit labels along the forward ray, and bootstrap transitivity through the self-similar stabilizer
target: fw-shell-inputs-at-window-zero-are-highly-transitive
requires:
  - fw-inputs-admit-no-twisted-shell-normalization
---

Notation as in the target. "Near equal" means equal off a finite set.

**Step 1: exact equivariance.** The proof of `fw-inputs-admit-no-twisted-shell-normalization`,
Steps 1 to 3, runs with the twisted action `g·(x,y) = (ρ_g x, ρ_(ψ(g)) y)`.
- The graph of `s` is commensurated, because `ρ_(ψ(g)) s ρ_g^-1` is near equal to `s`.
- FW gives an invariant `Γ'` at finite distance.
- As there, one obtains a cofinite set `N_1`, now `ρ(P)`-invariant, and an injection
  `s' : N_1 -> N`, near equal to `s`, with

      s'(ρ_g x) = ρ_(ψ(g)) s'(x)    for x ∈ N_1, g ∈ P.

- The orbit graph `x -> s'(x)` has a main ray `x_0 -> x_1 -> …` with every `x_j ∈ N_1`,
  containing all large `n`. Every other component is finite.

**Step 2: orbit labels (item 1).** For `x ∈ N_1`, the orbit `P·x` lies in `N_1`, and
`s'(P·x) = ψ(P)·s'(x) ⊆ P·s'(x)`. So `f(P·x) = P·s'(x)` is well defined on such orbits,
and `ℓ_j = P·x_j` satisfies `ℓ_(j+1) = f(ℓ_j)`.
- *Case 1: the `ℓ_j` are pairwise distinct.*
  - Then each `ℓ_j` meets the main ray only in `x_j`. So `ℓ_j ⊆ {x_j} ∪ Φ`, where `Φ` is
    the finite set of points off the main ray.
  - For `g ∈ P`, `ρ_g(x_j) ∈ ℓ_j`, and by injectivity only `|Φ|` indices `j` can have
    `ρ_g(x_j) ∈ Φ`. So `ρ_g` fixes almost every `x_j` and has finite support.
  - This contradicts the hypothesis for `g ≠ 1`.
- *Case 2: `ℓ_i = ℓ_(i+p)` for some `i`, with `p >= 1` minimal.*
  - Then `ℓ_(j+p) = ℓ_j` for all `j >= i`.
  - `O_r = ℓ_(i+r)`, `r ∈ Z/p`, are distinct infinite orbits covering every `x_j` with
    `j >= i`, hence a cofinite set.

**Step 3: one missing point.** Put `U = ⊔_r O_r`. Each `O_r` lies in `N_1`, since `N_1` is
`P`-invariant, and `s'(O_r) ⊆ O_(r+1)`.
- Since `s'` is near equal to `s`, for large `M` we have `|s'(U) ∩ [0,M]| = |U ∩ [0,M-1]|`.
  So `|U − s'(U)| = 1`.
- Hence `s'(O_r) = O_(r+1)` for all `r` except one, where exactly one point is missed.
- `σ = s'^p` maps each `O_r` injectively into itself, missing exactly one point `y_r`, and
  `σ ρ_g = ρ_(ψ^p(g)) σ` on `O_r`.
- `σ(O_r)` is `ρ(ψ^p(P))`-invariant and `O_r` is `P`-invariant, so `y_r` is fixed by
  `ψ^p(P)`.
- So `σ` is an isomorphism of `P`-sets `(O_r, ρ) -> (O_r − {y_r}, ρ∘ψ^p)`. This is the
  second sentence of item 2.

**Step 4: high transitivity (item 2).** Induction on `k`. `P` is transitive on `O_r`.
Suppose it is `k`-transitive.
- Transport through `σ`: `ψ^p(P)` is `k`-transitive on `O_r − {y_r}`.
- So the stabilizer of `y_r` in `P`, which contains `ψ^p(P)`, is `k`-transitive on
  `O_r − {y_r}`.
- A transitive group whose point stabilizer is `k`-transitive on the remaining points is
  `(k+1)`-transitive.

**Step 5: normal structure (item 3).**
- A normal subgroup `M` of `P` has orbits on `O_r` forming a `P`-invariant partition.
  `P` is 2-transitive, hence primitive, on `O_r`, so `M` is trivial or transitive on `O_r`.
- If `M` is trivial on every `O_r`, its elements have finite support, since `⋃ O_r` is
  cofinite. So `M = 1`.
- A finite `M` cannot be transitive on the infinite `O_r`.
- Let `z` be central. If `ρ_z(x) = y ≠ x` with `x ∈ O_r`, then every element of the
  stabilizer of `x` fixes `y`: `ρ_h y = ρ_h ρ_z x = ρ_z ρ_h x = y`. That contradicts
  2-transitivity on the infinite set `O_r`. So `z` is trivial on every `O_r`, and `z = 1`.

**The consequences.** Each is the cited statement combined with item 3:
- `λ I_N` is central in `E_N(R_L)`.
- A quotient of a Kazhdan group is Kazhdan, and (T) implies FW.
- If `K_2` is central, the centre of `St_N(R_L)` is `π^-1(Z(E_N(R_L)))`.
