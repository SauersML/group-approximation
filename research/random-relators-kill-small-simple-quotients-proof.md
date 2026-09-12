---
rg: 2
id: random-relators-kill-small-simple-quotients-proof
kind: route
title: Kazhdan spectral gap bounds point probabilities in every finite quotient, then a union bound over epimorphisms
target: random-relators-kill-small-simple-quotients-of-kazhdan-groups
requires: []
---

**Spectral gap.** Let `F` be a finite quotient of `Γ` with regular representation
`π` on `ℓ^2(F)`, and let `ℓ^2_0(F)` be the functions of mean zero. `F` acts
transitively, so `ℓ^2_0(F)` has no invariant vector. By property (T), every unit
vector `v ∈ ℓ^2_0(F)` has some `s ∈ S` with `||π(s)v - v|| >= κ`.

Put `P = (1/|S|) Σ_(s ∈ S) π(s)`. It is self-adjoint because `S` is symmetric,
and
`<(I - P)v, v> = (1/(2|S|)) Σ_s ||π(s)v - v||^2 >= κ^2/(2|S|)`.
So `spec(P|ℓ^2_0) ⊆ [-1, 1 - κ^2/(2|S|)]`, and the lazy operator
`P' = (I + P)/2` satisfies `spec(P'|ℓ^2_0) ⊆ [0, λ]` with `λ = 1 - κ^2/(4|S|)`.
The constant `λ` does not depend on `F`.

**Mixing bound.** The law of `χ(w_i)` is `x -> <P'^L δ_1, δ_x>`. Write
`u = 1/|F|` for the constant function. Then `P'^L u = u`, and `δ_1 - u` lies in
`ℓ^2_0`, so

```text
<P'^L δ_1, δ_x> = 1/|F| + <P'^L (δ_1 - u), δ_x - u>
               <= 1/|F| + λ^L ||δ_1 - u|| ||δ_x - u||
               <= 1/|F| + λ^L,
```

using `||δ_y - u||^2 = 1 - 1/|F| <= 1`. This proves part 1.

**Union bound.** Fix `N ⊴ Γ` with `Γ/N ≅ F` and `|F| <= λ^(-L)`. The events
`w_i ∈ N` are independent, and each has probability at most `2/|F|` by part 1
with `x = 1`. So all `k` relators lie in `N` with probability at most `(2/|F|)^k`.

A `d`-generated group has at most `|F|^d` homomorphisms to `F`. So the number of
`N` with `Γ/N ≅ F` is at most `|Epi(Γ,F)|/|Aut(F)| <= |F|^d`. Linearity of
expectation gives part 2.

**Alternating sum.** Put `a = k - d >= 1`. Then:
- `|Alt(5)| = 60`, and `|Alt(m+1)|/|Alt(m)| = m + 1 >= 6`;
- so `Σ_(m>=5) |Alt(m)|^(-a) <= 60^(-a) Σ_(j>=0) 6^(-aj) <= 2·60^(-a)`;
- hence `Σ_(m>=5) |Alt(m)|^d (2/|Alt(m)|)^k = 2^k Σ_m |Alt(m)|^(-a)
  <= 2^(k+1) 60^(-a) = 2^(d+1) 30^(-a)`.

When this is at most `ε`, Markov's inequality shows that with probability at
least `1 - ε` no alternating quotient of order at most `λ^(-L)` contains all
relators. By the surjection correspondence, none of them is then a quotient of
`Γ/<<w_1,...,w_k>>`. Finally, `m!/2 <= λ^(-L)` holds for every
`m <= (1 + o(1)) L log(1/λ)/log L`. `QED`
