---
rg: 2
id: kazhdan-regular-block-periodizations-of-mapping-tori-are-finite-proof
kind: route
title: Proof that regular block models of a Kazhdan mapping torus below min(kappa/sqrt2, sqrt3/L) are finite representations, by Kazhdan rigidity on Hilbert--Schmidt conjugation and a Mirsky rank count
target: kazhdan-regular-block-periodizations-of-mapping-tori-are-finite
requires:
  - fpbs-shalom-property-t-is-open
  - fp-mapping-torus-iff-finite-automorphic-presentation
  - mapping-torus-mf-radical-lies-in-finite-residual
artifacts:
  - research/kazhdan-regular-block-periodizations-of-mapping-tori-are-finite.md
---

Notation is as in the target. `‖·‖` is the operator norm and `‖X‖_2 = tr(X*X)^(1/2)` is the
unnormalized Hilbert--Schmidt norm, so `‖X‖_2 ≤ √n ‖X‖` on an `n`-dimensional space.

## 0. The presentation

`G` is finitely presented. By `fp-mapping-torus-iff-finite-automorphic-presentation`, `K` has a
finite automorphic presentation, and `G = <S, t | R_1, t s t^-1 = w_s>` with `R_1` finite and
`K = <S | φ^m(R_1), m in Z>`. Enumerate the relators of `K` as an increasing union of finite
sets `R_1 ⊂ R_2 ⊂ ...`. `K` is Kazhdan, so by `fpbs-shalom-property-t-is-open`, `<S | R_k>` is
Kazhdan for some `k`. Put `R_0 = R_k`. Every element of `R_0` is a relator of `G`, so `G` is
still presented by `<S, t | R_0, t s t^-1 = w_s>`.

Imported facts:

- **(Kaz)** For a unitary representation `σ` of `K~` on a Hilbert space `E`, with `P` the
  projection onto the invariant vectors, `‖ξ − Pξ‖ ≤ κ^-1 max_(s in S) ‖σ(s)ξ − ξ‖` for all `ξ`
  in `E`.

  *Proof.* `η = ξ − Pξ` lies in the invariant complement of the fixed space, which has no nonzero
  invariant vector. So `max_s ‖σ(s)η − η‖ ≥ κ‖η‖` by the definition of `κ`. Also
  `σ(s)η − η = σ(s)ξ − ξ`, because `σ(s)Pξ = Pξ`.
- **(EYM)** Eckart--Young--Mirsky: if `V` is unitary on `C^n` and `rank W ≤ r`, then
  `‖V − W‖_2² ≥ Σ_(j > r) s_j(V)² = n − r`.

## 1. Proof of (RB1)

Put `π = λ_Π ∘ θ` and `π' = λ_(Π') ∘ θ'`, both on `n`-dimensional spaces. Let `N = ker θ`,
`N' = ker θ'`, `c = [Π : θ(K~)]` and `c' = [Π' : θ'(K~)]`.

**Multiplicities.** The restriction of `λ_Π` to the subgroup `θ(K~)` is `c` copies of its regular
representation. So `π ≅ c · λ_(K~/N)`, and an irreducible representation `ρ` of `K~` occurs in `π`
with multiplicity

```text
m_ρ = c · dim ρ  if N ≤ ker ρ,     m_ρ = 0 otherwise.
```

The same holds for `π'`, with `m'_ρ`, `c'` and `N'`. Note that `n = c|K~/N| = c'|K~/N'|`.

**Rank bound.** The space of intertwiners `W : ℓ²(Π) -> ℓ²(Π')` (with `π'(g) W = W π(g)`) is
`⊕_ρ Hom(C^(m_ρ), C^(m'_ρ)) ⊗ id_ρ`. So every intertwiner has

```text
rank W  ≤  Σ_ρ min(m_ρ, m'_ρ) dim ρ.                                   (1)
```

Suppose `N ≠ N'`, and put `M = N N'`. If `m_ρ` and `m'_ρ` are both nonzero, then `ρ` factors
through `K~/M`. So the right side of (1) is at most

```text
Σ_(ρ in Irr(K~/M)) min(c, c') (dim ρ)²  =  min(c, c') |K~/M|.
```

Since `N ≠ N'`, at least one of `M ≠ N` or `M ≠ N'` holds, say `M ≠ N`. Then `[M : N] ≥ 2` and

```text
min(c, c')|K~/M|  ≤  c|K~/N|/2  =  n/2.
```

The case `M ≠ N'` is the same. So every intertwiner has rank at most `n/2`.

**Kazhdan step.** Let `K~` act on the Hilbert--Schmidt space `HS(ℓ²(Π), ℓ²(Π'))` by
`σ(g)X = π'(g) X π(g)*`. This is a unitary representation, and its invariant vectors are exactly
the intertwiners. For `s` in `S`:

```text
‖σ(s)V − V‖_2 = ‖π'(s)V − Vπ(s)‖_2 ≤ √n ‖π'(s) − Vπ(s)V*‖ < √n κ/√2.
```

By (Kaz), `W = PV` is an intertwiner with `‖V − W‖_2 < √n/√2`, that is `‖V − W‖_2² < n/2`. By
(EYM), `rank W > n/2`. This contradicts the rank bound, so `N = N'`. QED (RB1)

## 2. Proof of (RB2)

Fix `i`, put `j = τ i`, and define `θ'_i : F_S -> Π_j` by `θ'_i = θ_j ∘ ŵ`, so
`θ'_i(s) = θ_j(w_s)`. Block `j` of `U(w_s)` is `λ(θ'_i(s))`, and block `j` of `T U(s) T*` is
`V_i λ(θ_i(s)) V_i*`. So

```text
‖V_i λ(θ_i(s)) V_i* − λ(θ'_i(s))‖ ≤ δ   for s in S.                    (2)
```

**Step 1: `θ'_i` factors through `K~`.** Let `r ∈ R_0` have length `|r| ≤ L`. All the operators
in (2) are unitary, so a telescoping sum gives

```text
‖V_i λ(θ_i(r)) V_i* − λ(θ'_i(r))‖ ≤ |r| δ ≤ L δ < √3.
```

Here `θ_i(r) = 1`, so `x = θ'_i(r)` satisfies `‖λ(x) − 1‖ < √3`. If `x ≠ 1` has order `o ≥ 2`,
then `λ(x)` is a fixed-point-free permutation matrix and has every `o`-th root of unity as an
eigenvalue. So `‖λ(x) − 1‖ ≥ |e^(2πi⌊o/2⌋/o) − 1| ≥ √3`, which is impossible. Hence `x = 1`, and
`θ'_i` descends to a homomorphism `K~ -> Π_j`.

**Step 2: equal kernels.** `|Π_j| = |Π_i|` and `δ < κ/√2`, so (RB1), applied to `θ_i`, `θ'_i`
and `V_i`, gives `ker θ'_i = ker θ_i`. In particular `|θ'_i(K~)| = |H_i|`. Also
`θ'_i(K~) ≤ H_j`, since `θ'_i(s) = θ_j(w_s) ∈ H_j`. So `|H_i| ≤ |H_(τ i)|` for every `i`. Going
around each finite cycle of `τ` forces equality everywhere, hence `θ'_i(K~) = H_(τ i)`.

**Step 3: the isomorphisms.** `α_i(θ_i(g)) = θ'_i(g)` is well defined on `H_i`, because the
kernels agree. It is an isomorphism `H_i -> H_(τ i)`, and `α_i ∘ θ_i = θ_(τ i) ∘ ŵ` holds on
`F_S`.

**Step 4: the finite quotient.** Let `P = ∏_i H_i` and let `τ^ ∈ Aut(P)` be given by
`(τ^ x)_(τ i) = α_i(x_i)`. This is an automorphism because `τ` is a bijection and each `α_i` is an
isomorphism. Let `Q = P ⋊ <τ^>`. It is finite, because `Aut(P)` is finite. Define `Ψ` on the free
group on `S ∪ {t}` by `Ψ(s) = (θ_i(s))_i` and `Ψ(t) = τ^`. Then:

- for `r ∈ R_0`, `Ψ(r) = (θ_i(r))_i = 1`;
- `Ψ(t)Ψ(s)Ψ(t)^-1 = τ^((θ_i(s))_i)`, whose `τ i` coordinate is
  `α_i(θ_i(s)) = θ_(τ i)(w_s)`, the `τ i` coordinate of `Ψ(w_s)`.

So `Ψ` defines a homomorphism `G -> Q`, and `U(k) = ⊕_i λ(Ψ(k)_i)` for `k` in `K`, since both
sides are multiplicative in `k` and agree on `S`. QED (RB2)

## 3. Proof of (RB3)

`Ψ(K)` is a finite quotient of `K`, so it is trivial. Hence `θ_i(s) = Ψ(s)_i = 1` and `U(s) = 1`.

Every (LK3) witness, and every witness with `Rad_MF(G) = K × {0}`, has `K` without nontrivial
finite quotients. Indeed, by `mapping-torus-mf-radical-lies-in-finite-residual`, `K` lies in the
finite residual of `G`. A finite quotient `K -> F` would give a characteristic finite-index
subgroup `C ⊴ K` inside its kernel (`K` is finitely generated). Then `(K/C) ⋊ Z` is residually
finite, and it gives a finite quotient of `G` that is nontrivial on `K`. QED (RB3)

## 4. Remarks on sharpness of the hypotheses

- **Regular blocks are needed.** If the blocks are permutation representations `ℓ²(Π/Λ)`, (RB1)
  fails. Gassmann-equivalent `Λ, Λ'` give unitarily equivalent permutation representations with
  different marked stabilizer data. So the rank count, which uses that the multiplicity of `ρ` is
  `c·dim ρ` or `0`, is where the class ends.
- **Block-monomial `T` is needed.** For a general `T`, the multiset version of the argument bounds
  only the total multiplicity mismatch, `½ Σ_ρ |m_ρ − m'_ρ| dim ρ < (δ/κ)² dim H`. That is
  compatible with a Hamming-type wrap of relative size `1/p`, which is the sofic model. Whether an
  operator-norm `T` can realise such a mismatch is exactly the MF question for `G`.
