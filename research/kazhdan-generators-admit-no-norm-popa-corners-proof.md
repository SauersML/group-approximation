---
rg: 2
id: kazhdan-generators-admit-no-norm-popa-corners-proof
kind: route
title: The canonical vector of the finite-dimensional corner in the coarse bimodule is almost invariant under the conjugation representation, which is a multiple of the regular representation
target: kazhdan-generators-admit-no-norm-popa-corners
requires: []
artifacts:
  - research/artifacts/sk-popa-lgx-plan-2026-09-13.md
---

Complete proof (sk-popa-lgx, 2026-09-13). Notation as in the target claim. For `x ∈ M` write `x̂ = xδ_e ∈ L²(M) = ℓ²(Γ)`.

**Step 1: the coarse bimodule and the conjugation representation.**
- `H = L²(M) ⊗ L²(M)` is an `M`-bimodule, with `a·(ξ⊗η)·b = aξ ⊗ ηb`. The right action is right multiplication, `ηb = Jb*Jη`, which is bounded.
- Both actions are contractive: `‖aζ‖, ‖ζa‖ ≤ ‖a‖‖ζ‖`.
- `π(g)ζ = λ_gζλ_g*` is a unitary representation of `Γ` on `H`. On the basis, `π(g)(δ_h ⊗ δ_k) = δ_{gh} ⊗ δ_{kg^{-1}}`, because right multiplication by `λ_{g^{-1}}` sends `δ_k = λ_kδ_e` to `δ_{kg^{-1}}`.
- The action `g·(h,k) = (gh, kg^{-1})` of `Γ` on `Γ×Γ` is free. So `π` is a direct sum of copies of the regular representation, and it has no nonzero invariant vector since `Γ` is infinite.
- By the definition of a Kazhdan pair, every `ζ ∈ H` satisfies `max_{s∈S}‖π(s)ζ − ζ‖ ≥ ε‖ζ‖`.
- Since `‖π(s)ζ − ζ‖ = ‖(λ_sζ − ζλ_s)λ_s*‖ = ‖λ_sζ − ζλ_s‖`, this reads

  `max_{s∈S} ‖λ_sζ − ζλ_s‖ ≥ ε‖ζ‖` for all `ζ ∈ H`.   (K)

**Step 2: the canonical vector of `B`.**
- Write `B = ⊕_r M_{k_r}(C)` with matrix units `e^r_{ij}` in `M`, so `p = Σ_r Σ_i e^r_{ii}`. Put

  `ζ = Σ_r c_r Σ_{i,j} ê^r_{ij} ⊗ ê^r_{ji}`,  with `c_r = τ(p_r)^{-1/2}`, `p_r = Σ_i e^r_{ii}`.

- `ζ ≠ 0`, and `pζ = ζ = ζp`.
- **`ζ` commutes with `B`.** Take a matrix unit `e^r_{kl}`:
  - `e^r_{kl}ζ = c_r Σ_j ê^r_{kj} ⊗ ê^r_{jl}`;
  - `ζe^r_{kl} = c_r Σ_{i,j} ê^r_{ij} ⊗ (e^r_{ji}e^r_{kl})^ = c_r Σ_j ê^r_{kj} ⊗ ê^r_{jl}`;
  - matrix units of other blocks annihilate block `r` from both sides.
- **Norms.** The elementary tensors `ê^r_{ij} ⊗ ê^r_{ji}` are pairwise orthogonal. The `e^r_{ii}` are equivalent, so `τ(e^r_{ii}) = τ(p_r)/k_r`, and

  `‖ζ‖² = Σ_r c_r² Σ_{i,j} τ(e^r_{jj})τ(e^r_{ii}) = Σ_r c_r² τ(p_r)² = τ(p)`.

**Step 3: almost commutation.** Let `y ∈ M`, and choose `b ∈ B` with `‖pyp − b‖ = d := dist(pyp, B)`; it exists since `B` is finite-dimensional. Using `ζ = pζ = ζp`,

`yζ − ζy = (pyp − b)ζ − ζ(pyp − b) + (1−p)yp·ζ − ζ·py(1−p)`.

Here `(1−p)yp = (1−p)[y,p]` and `py(1−p) = −[y,p](1−p)`, so both have norm at most `‖[y,p]‖`. With the contractive actions,

`‖yζ − ζy‖ ≤ 2(d + ‖[y,p]‖)‖ζ‖`.   (A)

**Step 4: conclusion.** Put `y = λ_s` in (A) and combine with (K). For some `s ∈ S`,

`ε‖ζ‖ ≤ ‖λ_sζ − ζλ_s‖ ≤ 2(‖[λ_s,p]‖ + dist(pλ_sp, B))‖ζ‖`.

Since `ζ ≠ 0`, `max_s(‖[λ_s,p]‖ + dist(pλ_sp,B)) ≥ ε/2`. ∎

The corollary is proved in the claim node. The weights `c_r` are not needed here; they make the 2-norm transfer of `orthogonal-popa-corners-kazhdan-small-trace-proof` exact.
