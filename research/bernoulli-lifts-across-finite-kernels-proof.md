---
rg: 2
id: bernoulli-lifts-across-finite-kernels-proof
kind: route
title: The torsor's lifting cocycle is cohomologous to a homomorphism, and an invariant measure on the quotient group pins it to a finite-index splitting
target: bernoulli-lifts-across-finite-kernels-force-virtual-splitting
requires:
  - popa-bernoulli-cocycle-superrigidity
---

Complete proof. Let `X̃` be a free p.m.p. `W`-action with `X̃/N ≅ X = L^Q`.

0. **Diffuse base.** `L^Q × [0,1]^Q ≅ (L × [0,1])^Q` is a Bernoulli shift with diffuse base. It lifts to
   `X̃ × [0,1]^Q`, with `W` acting on the second factor through `Q`, and that lift is free because `X̃` is. So we may
   assume the base is diffuse, which is the form imported in `popa-bernoulli-cocycle-superrigidity`. Bernoulli shifts
   of an infinite group are mixing, so their restriction to the infinite subgroup `H` is weakly mixing.
1. **The lifting cocycle.** Fix a Borel transversal `M` of the `N`-orbits in `X̃`, and let `p_x ∈ M` be the point
   over `x ∈ X`. For `γ ∈ Q` there is a unique `c(γ, x) ∈ π^-1(γ)` with `c(γ, x) p_x = p_(γx)`, because `N` acts
   freely.
   - Uniqueness gives `c(γ_1 γ_2, x) = c(γ_1, γ_2 x) c(γ_2, x)`.
   - So `c : Q × X -> W` is a measurable cocycle into a countable discrete group, with `π(c(γ, x)) = γ`.
2. **Superrigidity.** By Popa's theorem (left cocycles are covered, arXiv:math/0512646v8 p. 4), there are a
   measurable `φ : X -> W` and a homomorphism `δ : Q -> W` with `c(γ, x) = φ(γx) δ(γ) φ(x)^-1` a.e.
3. **Project to `Q`.** Put `ψ = π ∘ φ` and `θ = π ∘ δ`. Then `ψ(γx) = γ ψ(x) θ(γ)^-1`.
   - So `ψ_* μ` is a probability measure on the countable set `Q`, invariant under the action
     `γ . g = γ g θ(γ)^-1`.
   - Invariant probability measures on countable sets charge only finite orbits. Pick `g` with `ψ_* μ({g}) > 0`.
     Its stabilizer `Q_0 = {γ : θ(γ) = g^-1 γ g}` has finite index.
4. **Splitting.** Fix `ĝ ∈ π^-1(g)` and put `δ'(γ) = ĝ δ(γ) ĝ^-1` for `γ ∈ Q_0`. Then `δ'` is a homomorphism with
   `π(δ'(γ)) = g θ(γ) g^-1 = γ`. So `Q_0' = δ'(Q_0)` is a complement to `N` in `π^-1(Q_0)`.

For the consequence on ascent: `Q_0'` has index `|N| [Q : Q_0]` in `W`, and maximality passes to subgroups and up
finite index.
