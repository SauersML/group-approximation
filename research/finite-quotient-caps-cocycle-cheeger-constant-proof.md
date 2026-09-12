---
rg: 2
id: finite-quotient-caps-cocycle-cheeger-constant-proof
kind: route
title: Regular action of the detecting quotient, diagonal indicator, and trickling down on the product covering
target: finite-quotient-caps-cocycle-cheeger-constant
requires: []
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

## Direct proof

This is steps 3--5 of Chapman--Peled's proof of Theorem 1.1 (arXiv:2509.21566v2,
pp. 22--23), with the soficity assumption removed and two normalizations made
explicit. The imported tools are their Lemma 2.9 and Corollary 2.14; the second
is Oppenheim's trickling-down theorem plus the weighted Cheeger inequality. Both
are quoted in the artifact.

**1. The cochain.** Let `ψ: π_1(Y,*) -> F` be a homomorphism to a finite group
with `ψ(∂Δ) != 1`, where `∂Δ` is the perimeter based at `*` through a spanning
tree `T`. Compose with the left-regular action of `F` to get `α: π_1(Y,*) ->
Sym(n)`, `n = |F|`. Since `ψ(∂Δ) != 1`, `α(∂Δ)` has no fixed point. Extend `α` to
a 1-cocycle of `Y` by putting `α = Id` on `T`. Then `α(σ ∂Δ σ̄) = α(∂Δ)` for every
tree path `σ`.

**2. Its defect on `Z`.** Every triangle of `Y` is satisfied, and `Δ` is violated
with `d_h(α(Δ),Id) = 1`. So, under the uniform triangle measure of `Z`,
`||δα||_Z = 1/|Z(2)|`.

**3. Distance to any cocycle of `Z`.** Let `β` be a 1-cocycle of `Z` on `N`
points. If `N < n`, pad `β` with fixed points. That only increases agreement
with `α`, so assume `N >= n`. Since `Δ in Z(2)`, `β(∂Δ) = Id`. Let `A` be the
covering of `G(Y)` associated with `α x β`, `D` its diagonal and `f = 1_D`.

* Lemma 2.9: `d_Y(α,β) >= ||δf|| / (2 μ_0(D))`.
* Claim 4.7: for each connected component `C` of `A`, the map
  `(y,i,i) -> (y, α(σΔσ̄)i, β(σΔσ̄)i) = (y, j, i)` with `j != i` is injective,
  stays in `C` and in the fibre over `y`, and leaves `D`. So
  `μ_0(C ∩ D) <= μ_0(C)/2`, and `f_C` is closer to `0` than to `1`.
* Each `C` is a connected covering of the λ-local spectral expander `Y`.
  Corollary 2.14 gives `||δf_C|| >= ((1-2λ)/(1-λ)) μ_0(C ∩ D)/μ_0(C)`. Averaging
  over components gives `||δf|| >= ((1-2λ)/(1-λ)) μ_0(D)`.

So `d_Y(α,β) >= (1-2λ)/(2-2λ)`.

**4. Changing measures.** Off the three edges of `Δ`, the descending edge
measure of `Z` is `(|Y(2)|/|Z(2)|)` times that of `Y`. On those edges the degree
grows by one. So `d_Z >= (|Y(2)|/|Z(2)|) d_Y`, and

```text
h_1(Z,Sym) <= ||δα||_Z / d_Z(α, Z^1) <= (1/|Z(2)|) / ((|Y(2)|/|Z(2)|)(1-2λ)/(2-2λ))
            = (2-2λ) / ((1-2λ)|Y(2)|).
```

No soficity, stability or randomness is used. ∎
