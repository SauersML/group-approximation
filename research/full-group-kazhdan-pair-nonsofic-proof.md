---
rg: 2
id: full-group-kazhdan-pair-nonsofic-proof
kind: route
title: Push the full-group copy through a sofic embedding, tensor with a sofic representation of L, and apply Theorem C
target: full-group-kazhdan-pair-noninvariant-fixed-algebra-is-nonsofic
requires:
  - kun-thom-free-nonsofic-action
---

# Proof

Suppose `G ↷ X` is sofic. Take `Θ : L^∞(X) ⋊ G → M_𝒰 = Π_(n→𝒰) M_(|Y_n|)` with `Θ(L^∞(X)) ⊆ D_𝒰` and
`σ(g) := Θ(u_g) ∈ 𝒮_𝒰` (Kun--Thom Definition 2.2). The action is free, so `L^∞(X) ⋊ G = L(R_G)`.

**Step 1, full-group elements go to permutations.** Let `T ∈ [R_G]`, with `X = ⊔_g A_g` and `T = g` on
`A_g`. In `L(R_G)`, `u_T = Σ_g 1_(gA_g) u_g` (2-norm convergent). The sets `gA_g` partition `X`, and so do
the `A_g`. For a finite set `F ⊆ G` put `v_F = Σ_(g∈F) Θ(1_(gA_g)) σ(g)`. Represent the projections
`Θ(1_(A_g))`, `g ∈ F`, by exactly orthogonal diagonal projections in each `M_(|Y_n|)`. Then
`σ(g)Θ(1_(A_g))σ(g)^* = Θ(1_(gA_g))` in `M_𝒰`, and the projections `Θ(1_(gA_g))`, `g ∈ F`, are orthogonal. So the
representing ranges `σ_n(g)P_(g,n)σ_n(g)^*` have pairwise overlaps of normalized size tending to `0` along `𝒰`.
Delete the overlapping points from the domains. This changes each representative by a 2-norm error tending to `0`
along `𝒰`, and `v_F` is represented by partial permutation matrices with orthogonal domains and ranges, of total
defect tending to `1 − μ(∪_F A_g)`. Complete each
of them to a permutation `p_(F,n)`; this changes the element by 2-norm at most `(2(1−μ(∪_F A_g)))^(1/2)`.
Letting `F` exhaust `G` along a diagonal sequence over `n`, `Θ(u_T)` is the limit of `(p_(F_n,n))_𝒰` in 2-norm.
Since `𝒮_𝒰` is 2-norm closed (a diagonal argument over `n`), `Θ(u_T) ∈ 𝒮_𝒰`.

**Step 2, a sofic embedding of the ρ-action.** Put `π(l) = Θ(u_(ρ(l))) ∈ 𝒮_𝒰`. It is multiplicative
because `Θ` is. `L` is sofic, so let `τ : L → 𝒮_(𝒰)'` be a sofic representation on sets `W_n`, with
`tr τ(l) = 0` for `l ≠ e`. On `Y_n × W_n` define

```text
Θ'(f) = Θ(f) ⊗ 1,     Θ'(u_l) = π(l) ⊗ τ(l).
```

Then `Θ'(f) ∈ D_𝒰 ⊗ D` (the diagonal), and `Θ'(u_l)` is a permutation. Covariance holds:
`π(l)Θ(f)π(l)^* = Θ(u_(ρ(l)) f u_(ρ(l))^*) = Θ(f ∘ ρ(l)^(-1))`. For the trace of `f u_l` with `l ≠ e`,
`tr(Θ(f)π(l) ⊗ τ(l)) = tr(Θ(f)π(l)) · tr τ(l) = 0`, which is the canonical trace of `f u_l` in the von Neumann
crossed product `L^∞(X) ⋊_ρ L`. For `l = e` it is `∫ f`. So `Θ'` is a trace-preserving `*`-homomorphism on
the algebraic crossed product, and it extends to an embedding of `L^∞(X) ⋊_ρ L`. So the action
`ρ : L ↷ X` is sofic in the sense of Definition 2.2.

**Step 3, Theorem C.** Kun--Thom Theorem C (quoted in `kun-thom-free-nonsofic-action`): if `Γ <= L` are
Kazhdan with `Γ` infranormal and `L ↷ X` is a sofic p.m.p. action, then `L^∞(X)^Γ` is `L`-invariant. The
statement and Definition 2.2 cover all p.m.p. actions, free or not. The mechanism is Proposition 3.1 for the
sofic representation `l ↦ Θ'(u_l)` together with `Θ'(L^∞(X)^Γ) ⊆ D_𝒰^(Θ'(Γ))`. So `L^∞(X)^(ρ(Γ))` is `ρ(L)`-invariant,
contradicting the hypothesis. ∎
