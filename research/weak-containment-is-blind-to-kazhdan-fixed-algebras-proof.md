---
rg: 2
id: weak-containment-is-blind-to-kazhdan-fixed-algebras-proof
kind: route
title: An invariant set of the contained action becomes an almost invariant set of the containing one, which a Kazhdan pair forbids
target: weak-containment-is-blind-to-kazhdan-fixed-algebras
requires: []
---

# Proof

**Definition in force** (Alpeev, arXiv:1706.01864v1, p. 5). `G ↷ (X, μ)` is weakly
contained in `G ↷ (Y, ν)` if for every finite set `A`, every measurable `f_1 : X → A` and
every `ε > 0` there is a measurable `f_2 : Y → A` whose process distribution on `A^G` is
`ε`-close to that of `f_1` in the weak-* topology.

**Proof.** Suppose `Γ` is not ergodic on `X`. Pick a `Γ`-invariant set `A_0 ⊆ X` with
`α = μ(A_0) ∈ (0, 1)`. Since `Γ` has property (T) it is finitely generated and has a
Kazhdan pair `(Q, κ)` with `Q` finite: every unitary representation with a unit vector `v`
satisfying `‖π(g)v − v‖ < κ` for all `g ∈ Q` has a nonzero invariant vector.

1. Apply weak containment to `f_1 = 1_(A_0)`, `A = {0, 1}`, and a small `δ > 0`. The
   distribution of `(f_1(g^(-1)x))_(g ∈ Q ∪ {1})` is determined by finitely many cylinder
   probabilities, so we get `B ⊆ Y` with `|ν(B) − α| < δ` and
   `ν(gB Δ B) < μ(gA_0 Δ A_0) + δ = δ` for all `g ∈ Q`.
2. Put `v = (1_B − ν(B)) / ‖1_B − ν(B)‖ ∈ L^2_0(Y)`. Then
   `‖1_B − ν(B)‖^2 = ν(B)(1 − ν(B)) >= α(1 − α)/2` for small `δ`, and
   `‖π(g)(1_B − ν(B)) − (1_B − ν(B))‖^2 = ν(gB Δ B) < δ`. So
   `‖π(g)v − v‖ < (2δ / (α(1−α)))^(1/2)`, which is `< κ` for small `δ`.
3. The Kazhdan pair gives a nonzero `Γ`-invariant vector in `L^2_0(Y)`, so `Γ` is not
   ergodic on `Y`. Contradiction.

**Mixing consequence.** If `G ↷ Y` is mixing and `Γ` is infinite, then for `A, B ⊆ Y` and
`γ → ∞` in `Γ`, `ν(γA ∩ B) → ν(A)ν(B)`, so `Γ` is ergodic on `Y`. The Kun--Thom actions
`({0,1},fair)^(G/Γ)` and its product with the Bernoulli shift have the nonconstant
`Γ`-invariant function `x ↦ x_Γ`, so neither is weakly contained in any mixing action of `G`.

**Ultrapowers.** A factor of an ultrapower of `Y` has its observables approximated by
observables of `Y` along the ultrafilter, so it is weakly contained in `Y`.
