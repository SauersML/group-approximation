---
rg: 2
id: kazhdan-multiplicity-rigidity-kills-exact-cover-models-proof
kind: route
title: Proof by operator-norm Kazhdan projections on ρ ⊗ σ̄, an exact intertwiner at the wrap, the finite automorphic presentation, and Malcev
target: kazhdan-multiplicity-rigidity-kills-exact-cover-models
requires:
  - fpbs-shalom-property-t-is-open
  - fp-mapping-torus-iff-finite-automorphic-presentation
  - mapping-torus-mf-radical-lies-in-finite-residual
  - finitely-generated-linear-groups-are-residually-finite
artifacts:
  - research/kazhdan-multiplicity-rigidity-kills-exact-cover-models.md
  - research/kazhdan-regular-block-mapping-torus-models-are-finite-proof.md
---

Notation is as in the target. `‖·‖` is the operator norm throughout. `S± = S ∪ S^-1`, `q = |S±|`.

## 0. The presentation

This is section 0 of `kazhdan-regular-block-mapping-torus-models-are-finite-proof`, which uses
`fp-mapping-torus-iff-finite-automorphic-presentation` and `fpbs-shalom-property-t-is-open`:
`G = <S, t | R_0, t s t^-1 = w_s>` with `R_0` finite and `K~ = <S | R_0>` Kazhdan. Each `r` in
`R_0` is a relator of `K`, and `ŵ(r)` represents `φ(r) = 1` in `K`. So every element of
`R_1 = R_0 ∪ ŵ(R_0)` is a relator of `K`, and `K` is a quotient of `K~_1 = <S | R_1>`, which is a
quotient of `K~`.

`(S, κ)` is a Kazhdan pair for `K~`: for every unitary representation `π` of `K~` and every
vector `ξ` orthogonal to the `π`-invariant vectors, `max_(s in S) ‖π(s)ξ − ξ‖ ≥ κ‖ξ‖`.

## 1. The spectral gap of the Kazhdan average

For a unitary representation `π` of `K~` on `E`, put

```text
h_π  = (1/q) Σ_(s in S±) π(s),        h'_π = (1 + h_π)/2.
```

`h_π` is self-adjoint with `‖h_π‖ ≤ 1`, since `S±` is symmetric. So `0 ≤ h'_π ≤ 1`. Let `P_π` be
the projection onto the invariant vectors `E^π`, and `E_0 = (E^π)^⊥`. `E_0` is `π`-invariant,
so `h'_π` preserves it. `h'_π = 1` on `E^π`.

**Claim.** `⟨h'_π ξ, ξ⟩ ≤ (1 − γ)‖ξ‖²` for `ξ ∈ E_0`, where `γ = κ²/(4q)`.

*Proof.* Let `‖ξ‖ = 1`. Some `s ∈ S` has `‖π(s)ξ − ξ‖ ≥ κ`. Since
`‖π(s)ξ − ξ‖² = 2 − 2 Re⟨π(s)ξ, ξ⟩`, that term has `Re⟨π(s)ξ, ξ⟩ ≤ 1 − κ²/2`. Every other term
of the average has real part at most `1`. So `⟨h_π ξ, ξ⟩ ≤ 1 − κ²/(2q)`, and
`⟨h'_π ξ, ξ⟩ ≤ 1 − κ²/(4q)`. ∎

`h'_π` is positive on `E_0`, so `‖h'_π|_(E_0)‖ ≤ 1 − γ`. Hence, for every `m ≥ 1`,

```text
‖ h'_π^m − P_π ‖  ≤  (1 − γ)^m  ≤  e^(−γ m).                         (1)
```

With `m_0 = ⌈ln 4 / γ⌉ = ⌈4 q ln 4 / κ²⌉`, the right side is at most `1/4`.

## 2. Proof of (MR)

Let `α, β` act on `C^k`, and put `δ = max_(s in S) ‖α(s) − β(s)‖ < δ_0 = 1/m_0`. Since `‖α(s)* − β(s)*‖ = ‖α(s) − β(s)‖`, the same bound
holds on `S±`.

Fix an irreducible unitary representation `σ` of `K~` on a finite-dimensional space `H_σ`.
Consider `π_α = α ⊗ σ̄` and `π_β = β ⊗ σ̄` on the same space `E = C^k ⊗ \bar(H_σ)`. Identify
`E` with `Hom(H_σ, C^k)`, where `g` acts by `X ↦ α(g) X σ(g)*`. Then the invariant vectors of
`π_α` are the intertwiners `Hom_(K~)(σ, α)`. By Schur's lemma and complete reducibility, this
space has dimension `m_σ(α)`, the multiplicity of `σ` in `α`. The same holds for `β`.

**Closeness.** For `s ∈ S±`, `‖π_α(s) − π_β(s)‖ = ‖(α(s) − β(s)) ⊗ σ̄(s)‖ ≤ δ`. So

```text
‖h'_(π_α) − h'_(π_β)‖  ≤  δ/2.
```

Both operators are contractions, so `‖A^m − B^m‖ ≤ m ‖A − B‖` (telescoping) gives
`‖h'^(m_0)_(π_α) − h'^(m_0)_(π_β)‖ ≤ m_0 δ/2 < 1/2`.

**Projections.** By (1) and the triangle inequality,

```text
‖P_(π_α) − P_(π_β)‖  ≤  1/4 + m_0 δ/2 + 1/4  <  1.
```

Two projections `P, Q` with `‖P − Q‖ < 1` have equal rank. Indeed, if `Qx = x` and `Px = 0`,
then `‖x‖ = ‖(Q − P)x‖ < ‖x‖` unless `x = 0`. So `P` is injective on `ran Q`, which gives
`rank Q ≤ rank P`, and symmetrically. Hence `m_σ(α) = m_σ(β)`.

This holds for every irreducible `σ`. Finite-dimensional unitary representations are direct
sums of irreducibles and are determined up to unitary equivalence by their multiplicities. So
`α ≅ β`. The constant `δ_0` depends only on `κ` and `q`, not on `k` or `σ`. ∎ (MR)

## 3. Proof of (EC)

Put `α(s) = T U(s) T*` and `β(s) = U(w_s)`, that is `β = U ∘ ŵ`.

- `α` is a representation of `K~`, because `U` kills `R_0 ⊆ R_1`.
- `β` is a representation of `K~`: for `r ∈ R_0`, `β(r) = U(ŵ(r)) = 1`, because
  `ŵ(r) ∈ R_1`. Here `β(r)` means the word `r` evaluated at the `β(s)`. That equals `U(ŵ(r))`,
  because `ŵ` is a homomorphism of free groups.

By hypothesis, `max_s ‖α(s) − β(s)‖ < δ_0`. So by (MR) there is a unitary `V` with
`V α(s) V* = β(s)` for all `s`. Put `T' = V T`. Then

```text
T' U(s) T'^*  =  U(w_s)     for all s in S.
```

So `s ↦ U(s)`, `t ↦ T'` satisfies every relator of the presentation of section 0: `R_0`
because `R_0 ⊆ R_1`, and `t s t^-1 = w_s` by the display. It therefore defines a homomorphism
`Ψ : G -> U(k)`. Its restriction to `K = <<S>>_G` agrees with `U` on `S`, so `U` factors
through `K`.

**Quotientless `K`.** `Ψ(K)` is a finitely generated subgroup of `GL_k(C)`, so it is residually
finite by `finitely-generated-linear-groups-are-residually-finite`. It is a quotient of `K`. If it
were nontrivial, it would have a nontrivial finite quotient, which would be a nontrivial finite
quotient of `K`. So `Ψ(K) = 1`, and `U(s) = 1` for all `s`. If every block of `U` has finite
image, `Ψ(K)` is already finite and Malcev is not needed. ∎ (EC)

## 4. Proof of (GP)

Let `U` be a `c`-gapped representation of `K~`, and let the defect be
`δ < min(δ_0, c/L)`. Let `r = s_1^(e_1) ⋯ s_ℓ^(e_ℓ) ∈ R_0`, with `ℓ ≤ L`. Then

```text
T U(r) T* = ∏_i (T U(s_i) T*)^(e_i),     U(ŵ(r)) = ∏_i U(w_(s_i))^(e_i).
```

Corresponding factors are unitaries at distance at most `δ` (for `e_i = −1`, use
`‖A* − B*‖ = ‖A − B‖`). Telescoping gives `‖U(ŵ(r)) − T U(r) T*‖ ≤ ℓδ < c`. Since
`U(r) = 1`, this says `‖U(ŵ(r)) − 1‖ < c`, so `U(ŵ(r)) = 1` by the gap. Hence `U` kills `R_1`,
and (EC) applies because `δ < δ_0`.

**Permutation blocks are `√3`-gapped.** Let `U` be a direct sum of permutation representations
`ℓ²(X_i)` of `K~` on finite sets, possibly conjugated by one fixed unitary (which does not change
`‖U(x) − 1‖`). Then `U(x)` is the permutation matrix of a permutation of `X = ⊔ X_i`. If
`U(x) ≠ 1`, the permutation has a cycle of some length `ℓ ≥ 2`. On the span of that cycle,
`U(x)` has every `ℓ`-th root of unity as an eigenvalue, in particular `ζ = e^(2πi⌊ℓ/2⌋/ℓ)`.
Since `⌊ℓ/2⌋/ℓ ∈ [1/3, 1/2]`, `|ζ − 1| = 2 sin(π⌊ℓ/2⌋/ℓ) ≥ 2 sin(π/3) = √3`. So
`‖U(x) − 1‖ ≥ √3`. This covers regular blocks `λ_Π ∘ θ`, arbitrary multiplicities, and
Gassmann-equivalent permutation blocks `ℓ²(Π/Λ)`. ∎ (GP)

## 5. Proof of (AS)

The norm corona is `Q = ∏ M_(k_n) / ⊕ M_(k_n)`, with `‖[x_n]‖ = limsup_n ‖x_n‖`. Every unitary
of `Q` lifts to a sequence of unitaries. Indeed, if `x_n` lifts `u`, then `x_n* x_n → 1`, so
`x_n` is invertible for large `n`. Replace `x_n` by its polar unitary for those `n`, and by `1`
for the finitely many others.

Let `T_n` be a unitary lift of `Θ(t)`. By hypothesis `(ρ_n(s))_n` lifts `Θ(s)`, and
`(ρ_n(w_s))_n` lifts `Θ(w_s)` because `ρ_n` is multiplicative. So the class of
`(T_n ρ_n(s) T_n* − ρ_n(w_s))_n` is `Θ(t)Θ(s)Θ(t)* − Θ(w_s) = 0`. Hence

```text
δ_n = max_(s in S) ‖T_n ρ_n(s) T_n* − ρ_n(w_s)‖  ->  0.
```

For `n` large, `δ_n < δ_0`. Then (EC), applied to `U = ρ_n` and `T = T_n`, gives
`ρ_n(s) = 1`. So `Θ(s) = [(ρ_n(s))_n] = 1` for every `s` in `S`, and `Θ|_K` is trivial.

For `√3`-gapped representations `ρ_n` of `K~`, use (GP) instead, for `n` with
`δ_n < min(δ_0, √3/L)`. ∎ (AS)

## 6. Proof of (RL)

`Rad_MF(G)` is the intersection of the kernels of all norm-corona models of `G`.

- `Z` is MF, so composing `G -> Z` with a faithful corona model of `Z` gives a model with kernel
  `K × {0}`. Hence `Rad_MF(G) ⊆ K × {0}` always.
- If every model is `R_1`-liftable on `K`, then (AS) makes every model trivial on `K`. So
  `K × {0} ⊆ Rad_MF(G)`.
- Conversely, if `Rad_MF(G) = K × {0}`, every model is trivial on `K`, and `ρ_n = 1` is an
  `R_1`-lift. ∎ (RL)

## 7. The LEF application

Let `ι_n : B(r_n) -> Q_n` be local embeddings of the balls of radius `r_n` of `K` (for `S`)
into finite groups. Set `θ_n(s) = ι_n(s)`, extended to a homomorphism `F_S -> Q_n`.

Let `x = s_1^(e_1) ⋯ s_ℓ^(e_ℓ)` be a relator of `K` with `ℓ ≤ r_n`. All prefixes of `x` lie in
`B(r_n)`, and `ι_n` is a partial homomorphism there. By induction on prefixes,
`θ_n(x) = ι_n(x) = ι_n(1) = 1`.

The elements of `R_1` are relators of `K` of length at most `L · max_s |w_s|`. So for
`r_n ≥ L · max_s |w_s|`, every `π_n ∘ θ_n` kills `R_1`, for any unitary representation `π_n` of
`Q_n`. Then (AS) applies to any corona model `Θ` of `G` with `Θ(s) = [(π_n(θ_n(s)))_n]`. Here
`Ψ(K)` is finite, so Malcev is not used. ∎
