---
rg: 2
id: bounded-removal-finite-quotient-cheeger-cap-proof
kind: route
title: Regular action of the detecting quotient of the complex minus t triangles, then trickling down on the product covering
target: bounded-removal-finite-quotient-caps-cocycle-cheeger
requires: []
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

## Direct proof

This repeats `finite-quotient-caps-cocycle-cheeger-constant-proof` with `t`
removed triangles. The imported tools are Chapman--Peled's Lemma 2.9 and
Corollary 2.14 (arXiv:2509.21566v2), both quoted in the artifact.

**1. The cochain.** Let `ψ: π_1(Y',*) -> F` be a homomorphism to a finite group
with `ψ(∂Δ) != 1`, where `∂Δ` is the perimeter of the detected triangle
`Δ in T`, based at `*` through a spanning tree of the common 1-skeleton. Compose
with the left-regular action of `F` to get `α: π_1(Y',*) -> Sym(n)`, `n = |F|`.
Then `α(∂Δ)` has no fixed point. Extend `α` to a 1-cocycle of `Y'` by `α = Id` on
the tree. Every edge of `Z` is an edge of `Y'`, so `α` is a 1-cochain of `Z`, and
`α(σ ∂Δ σ̄) = α(∂Δ)` for every tree path `σ`.

**2. Its defect on `Z`.** Every triangle of `Y'` is satisfied, and each of the
`t` triangles of `T` contributes at most `1` to the coboundary norm. Under the
uniform triangle measure of `Z`,

```text
||δα||_Z <= t / |Z(2)|.
```

**3. Distance to any cocycle of `Z`.** Let `β` be a 1-cocycle of `Z` on `N`
points. If `N < n`, pad `β` with fixed points, which only increases agreement with
`α`; so assume `N >= n`. Since `Δ in Z(2)`, `β(∂Δ) = Id`. Both `α` and `β`
restrict to 1-cocycles of `Y'`. Let `A` be the covering of `Y'` associated with
`α x β`, `D` its diagonal and `f = 1_D`.

* Lemma 2.9: `d_(Y')(α,β) >= ||δf|| / (2 μ_0(D))`, with the measures of `Y'`.
* Claim 4.7 of the source, with the same injection: for each connected component
  `C` of `A`, `(y,i,i) -> (y, α(σΔσ̄)i, β(σΔσ̄)i) = (y,j,i)` with `j != i` stays in
  `C` and in the fibre over `y`, and leaves `D`. So `μ_0(C ∩ D) <= μ_0(C)/2`.
  Only `Δ`, the cocycle property of `α` on `Y'` and `β(∂Δ) = Id` are used.
* Each `C` is a connected covering of the λ-local spectral expander `Y'`.
  Corollary 2.14 gives `||δf_C|| >= ((1-2λ)/(1-λ)) μ_0(C ∩ D)/μ_0(C)`, and averaging
  over components gives `||δf|| >= ((1-2λ)/(1-λ)) μ_0(D)`.

So `d_(Y')(α,β) >= (1-2λ)/(2-2λ)`.

**4. Changing measures.** The descending edge measure of a pure complex `X` is
`μ_1^X(e) = deg_X(e) / (3|X(2)|)`, where `deg_X(e)` counts triangles containing
`e`. Since `Y'(2) ⊂ Z(2)` and the 1-skeleta agree, `deg_Z(e) >= deg_(Y')(e)`, so
`μ_1^Z(e) >= (|Y'(2)|/|Z(2)|) μ_1^(Y')(e)` for every edge. Hence
`d_Z(α,β) >= (|Y'(2)|/|Z(2)|) d_(Y')(α,β)` for every cocycle `β` of `Z`, and

```text
h_1(Z,Sym) <= ||δα||_Z / d_Z(α, Z^1(Z,Sym))
           <= (t/|Z(2)|) / ((|Y'(2)|/|Z(2)|) (1-2λ)/(2-2λ))
            = (2-2λ) t / ((1-2λ)|Y'(2)|).
```

No soficity, stability or randomness is used. ∎
