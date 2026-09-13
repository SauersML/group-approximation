---
rg: 2
id: simple-kazhdan-bernoulli-host-via-popa-superrigidity
kind: route
title: Untwist the containment cocycle by Popa superrigidity and use simplicity to make the untwisted morphism injective
target: simple-kazhdan-bernoulli-relation-hosts-contain-the-group
requires: []
artifacts:
  - research/artifacts/solve-sofic-actions-2026-09-13.md
---

# Proof

1. **The containment cocycle.** For `h ∈ H` and `g ∈ G` the set
   `E_(h,g) = {y : θ(h·y) = g·θ(y)}` is measurable. By containment every `y`
   (off a null set) lies in some `E_(h,g)`, and by essential freeness of
   `G ↷ X` in at most one. So `c(h,y) := ` the unique `g` with
   `θ(h·y) = g·θ(y)` is a measurable map `H × Y → G`, defined off a null set.
   Applying uniqueness to
   `θ(h_1h_2·y) = c(h_1,h_2·y)·θ(h_2·y) = c(h_1,h_2·y)c(h_2,y)·θ(y)` gives the
   cocycle identity `c(h_1h_2,y) = c(h_1,h_2·y)c(h_2,y)` for a.e. `y`.
2. **Popa's theorem applies.** `H` is an infinite normal subgroup of itself with
   property (T), hence with the relative property (T), so `H` is w-rigid in
   Popa's sense. The Bernoulli action `H ↷ [0,1]^H` is s-malleable (Popa's own
   example in the abstract) and weak mixing, since `H` is infinite. The target
   `G` is countable discrete. By the abstract of arXiv:math/0512646 (verbatim in
   the artifact), `c` is cohomologous to a group morphism `ρ : H → G`. There is
   a measurable `φ : Y → G` with `c(h,y) = φ(h·y) ρ(h) φ(y)^(-1)` for all `h`
   and a.e. `y`. With the opposite cocycle convention, replace `φ` by
   `y ↦ φ(y)^(-1)`; the argument below is unchanged.
3. **The equivariant map.** Put `ψ(y) := φ(y)^(-1)·θ(y) ∈ X`. Then for all
   `h` and a.e. `y`,
   `ψ(h·y) = φ(h·y)^(-1)·θ(h·y) = φ(h·y)^(-1) c(h,y)·θ(y) = ρ(h) φ(y)^(-1)·θ(y) = ρ(h)·ψ(y)`.
4. **Injectivity.** `N := ker ρ` is normal in the simple group `H`, so `N = 1`
   or `N = H`. Suppose `N = H`. Then `ψ` is `β`-invariant. Bernoulli shifts of
   infinite groups are ergodic and `X` is standard Borel, so `ψ` is essentially
   constant, say `x_0`. Then `θ(y) = φ(y)·x_0 ∈ G·x_0` for a.e. `y`, so the
   countable set `G·x_0` has full `μ_A`-measure.
   This is impossible. Essentially free `H`-orbits in `A` are infinite, and
   they lie in `G`-orbits, so `G` is infinite. Then `μ` has no atoms: an atom's
   `G`-orbit is infinite by freeness, and all of its points carry the same
   positive mass by invariance, which would give infinite total mass. So
   `N = 1`, and `ρ` is injective. ∎
