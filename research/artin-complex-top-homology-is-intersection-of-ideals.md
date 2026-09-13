---
rg: 2
id: artin-complex-top-homology-is-intersection-of-ideals
kind: claim
title: "The top homology of the Artin complex of A_S is the left ideal of ZA cut out by the elements 1 - s, s in S"
---

Let `A = A_Γ` be an Artin group on a finite set `S` with `n = |S| ≥ 2`, and write
`P_s = A_{S∖{s}}` for the maximal standard parabolic subgroups. The **Artin complex**
`Δ(A)` is the simplicial complex whose vertices are the cosets `gP_s` (`g ∈ A`,
`s ∈ S`), a finite set of vertices spanning a simplex when the cosets have a common
element. `A` acts by left translation.

1. `Δ(A)` has dimension `n − 1`. `A` acts simply transitively on the `(n − 1)`-simplices
   `σ_g = {gP_s : s ∈ S}`, and for each `s ∈ S` the `(n − 2)`-simplices missing type `s`
   are indexed by the cosets `g⟨s⟩`.
2. `H_{n−1}(Δ(A); Z) ≅ ⋂_{s ∈ S} ZA·(1 − s)` as left `ZA`-modules.
3. If the Coxeter group `W` is finite, the element
   `x_W = Σ_{w ∈ W} (−1)^{ℓ(w)} σ(w)` lies in this intersection and is nonzero. Here
   `σ(w) ∈ A` is the positive lift of any reduced expression of `w`.

So the top homology of the Artin complex is a concrete ideal of the group ring: the
`x ∈ ZA` whose coefficients sum to zero along every coset `g⟨s⟩` of every generator.
For finite `W` it contains the alternating sum over `W`. For infinite `W` it vanishes
whenever the K(π,1) conjecture holds for `A` (see
`deligne-connectivity-iff-artin-complex-connectivity`), and in particular
unconditionally when every subset of `S` generating a finite Coxeter group has at most
two elements. Whether it vanishes for every infinite `W` is a ring-theoretic test of the
top-degree part of that conjecture.

On the direct side of Zaremsky Problem 1.5 this is the top-degree input of the
Artin-complex version of Brown's criterion (see the Attempts of
`every-free-of-infinity-artin-group-is-type-f-infinity`). Proof route:
`artin-complex-top-homology-is-intersection-of-ideals-proof`.
