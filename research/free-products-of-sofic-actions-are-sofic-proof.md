---
rg: 2
id: free-products-of-sofic-actions-are-sofic-proof
kind: route
title: Randomize factor labels, match equal labels across factors, and compose conjugated factor models along reduced words
target: free-products-of-sofic-actions-are-sofic
requires: []
artifacts:
  - research/artifacts/free-products-of-sofic-actions-2026-09-16.md
---

This is a complete direct proof. It uses only GKP Definition 2.1 and
elementary counting.

## Conventions

For a finite set `A`, `d(σ,τ) = |{a : σa ≠ τa}| / |A|` is the normalized
Hamming distance on `Sym(A)`. Three facts are used.

- (H1) `d(ρσ, ρτ) = d(σ,τ) = d(σρ, τρ)`.
- (H2) `d(στ, σ'τ') <= d(σ,σ') + d(τ,τ')`.
- (H3) On `A × T`, `d(σ × id_T, τ × id_T) = d(σ,τ)`.

**GKP Definition 2.1** (arXiv:2401.04945v3). A map `φ : G → Sym(A)` is
*unital* if `φ(1) = id`. It is *`(F,ε)`-multiplicative* if
`d(φ(gh), φ(g)φ(h)) < ε` for all `g,h ∈ F`. It is an *`(F,E,ε)`-orbit
approximation* of `α : G ↷ X` if there are a finite set `B`, a subset
`S ⊆ A` with `|S| > (1-ε)|A|`, and injective maps `π_s : E → B` (`s ∈ S`),
such that `π_(φ(g)s)(x) = π_s(α(g^-1)x)` for all `s ∈ S`, `g ∈ F`, `x ∈ E`
with `φ(g)s ∈ S` and `α(g^-1)x ∈ E`. The action `α` is *sofic* if such a `φ`
exists for every finite `F ⊆ G`, finite `E ⊆ X` and `ε > 0`.

Write `gx` for `α(g)x`. Every `g ∈ G = *_(i∈I) G_i` has a unique reduced
form `g = g_1 g_2 ⋯ g_k` with `k = ℓ(g) >= 0`, `g_t ∈ G_(i_t) \ {1}` and
`i_t ≠ i_(t+1)`. Its entries `g_t` are the *syllables* of `g`.

## Step 0: data

Fix finite `F ⊆ G`, `E ⊆ X` and `ε > 0`.

Let `J ⊆ I` be the set of indices `i_t` of syllables of elements of `F`.
- If `J = ∅`, then `F ⊆ {1}`. The one-point set `A = {a}` with `φ ≡ id`,
  `S = A`, `B = E` and `π_a = id_E` works.
- Otherwise `J` is finite and nonempty. Put `m = |J|`, and fix one reference
  index in `J`, written `1`.

Put

```text
ℓ_max = max_(g∈F) ℓ(g),         Ł = Σ_(g∈F) ℓ(g),
F_j   = { g_t : g ∈ F, i_t = j }  ⊆ G_j            (j ∈ J),
E'    = { (g_1⋯g_(t-1))^-1 x : x ∈ E, g ∈ F, 1 <= t <= ℓ(g)+1 } ∪ E.     (FP0)
```

These are finite. Fix `δ > 0` with

```text
(ℓ_max + 1) δ < ε      and      (1 + Ł)(m + 1) δ < ε.                    (FP1)
```

## Step 1: factor models

For each `j ∈ J`, the hypothesis that `α_j` is sofic gives the following.
- A finite set `A_j` and a unital, `(F_j,δ)`-multiplicative
  `φ_j : G_j → Sym(A_j)`.
- A good set `S_j ⊆ A_j` with `|S_j| > (1-δ)|A_j|`, and injective labels
  `Λ^j_p : E' → B_j` for `p ∈ S_j`. They satisfy

```text
Λ^j_(φ_j(h)p)(y) = Λ^j_p(h^-1 y)
   whenever p ∈ S_j, h ∈ F_j, y ∈ E', φ_j(h)p ∈ S_j, h^-1 y ∈ E'.         (FM)
```

## Step 2: randomized models of a common size

Fix a nonempty finite set `B'` with `|B'| >= |E'|^2 / δ`. Put `L = B'^(E')`, the set of
all maps `E' → B'`, and let `L_inj ⊆ L` be the injective ones. Put
`T_j = B'^(B_j)`. Put `N = Π_(j∈J) |A_j × T_j|` and `M_j = N / |A_j × T_j|`,
an integer. Define

```text
A'_j = A_j × T_j × [M_j]                  (so |A'_j| = N),
φ'_j(h)(p, τ, r) = (φ_j(h)p, τ, r)         (h ∈ G_j),
S'_j = S_j × T_j × [M_j],
λ^j(p, τ, r) = τ ∘ Λ^j_p ∈ L               (p ∈ S_j).                       (FP2)
```

For `p ∉ S_j`, let `λ^j(p,τ,r)` be a fixed element of `L`; its value is never
used.

**(R1)** `φ'_j` is unital and `(F_j,δ)`-multiplicative, and
`|S'_j| > (1-δ)N`. This follows from (H3).

**(R2) Exact equivariance.** Suppose `b ∈ S'_j`, `h ∈ F_j`,
`φ'_j(h)b ∈ S'_j`, `y ∈ E'` and `h^-1 y ∈ E'`. Then
`λ^j(φ'_j(h)b)(y) = λ^j(b)(h^-1 y)`.

*Proof.* Write `b = (p,τ,r)`. Then `φ'_j(h)b = (φ_j(h)p, τ, r)` with
`p, φ_j(h)p ∈ S_j`. By (FM),
`τ(Λ^j_(φ_j(h)p)(y)) = τ(Λ^j_p(h^-1 y))`.

**(R3) Uniform labels.** For every `c ∈ L`,
`|{ b ∈ S'_j : λ^j(b) = c }| = |S'_j| / |L|`.

*Proof.* Fix `p ∈ S_j` and `r`. Since `Λ^j_p` is injective, the map
`τ ↦ τ ∘ Λ^j_p` from `B'^(B_j)` to `B'^(E')` is onto. Every fibre has
`|B'|^(|B_j| - |E'|)` elements, because `τ` is free off the image of
`Λ^j_p`. Summing over `p ∈ S_j` and `r ∈ [M_j]` gives
`|S_j| M_j |B'|^(|B_j|-|E'|) = |S'_j| / |L|` for each `c`.

**(R4) Few non-injective labels.** A map `E' → B'` fails to be injective only
if two of the `binom(|E'|,2)` pairs of points collide. So
`|L \ L_inj| / |L| <= binom(|E'|,2) / |B'| < δ`. By (R3),
`|{ b ∈ S'_j : λ^j(b) ∉ L_inj }| < δ N`.

## Step 3: matching labels across factors

Put `A = A'_1`, so `|A| = N`, and put `β_1 = id_A` and `D_1 = S'_1`.

Now fix `j ∈ J \ {1}`. By (R3), each label class `c ∈ L` has
`|S'_1|/|L|` elements in `S'_1` and `|S'_j|/|L|` elements in `S'_j`. For
each `c`, choose an injection from `min(|S'_1|,|S'_j|)/|L|` elements of the
class of `c` in `S'_1` into the class of `c` in `S'_j`.

The union of these injections is an injective map `β°_j : D_j → S'_j` with
`D_j ⊆ S'_1`. It satisfies

```text
λ^j(β°_j a) = λ^1(a)  (a ∈ D_j),        |D_j| = min(|S'_1|,|S'_j|) > (1-δ)N.   (FP3)
```

Extend `β°_j` to a bijection `β_j : A → A'_j`. This is possible because both
sets have `N` elements.

## Step 4: the map φ

For `j ∈ J` and `h ∈ G_j`, put `ψ_j(h) = β_j^-1 φ'_j(h) β_j ∈ Sym(A)`. For
`i ∉ J`, put `ψ_i ≡ id_A`. For `g = g_1⋯g_k` reduced with `g_t ∈ G_(i_t)`, put

```text
φ(g) = ψ_(i_1)(g_1) ψ_(i_2)(g_2) ⋯ ψ_(i_k)(g_k).                            (FP4)
```

Then `φ(1) = id`, the empty product. By (H1) and (R1), each `ψ_j` with
`j ∈ J` is unital and `(F_j,δ)`-multiplicative. Below, `ψ(x)` means `ψ_i(x)`
for the factor `G_i` containing a syllable `x`.

## Step 5: multiplicativity

Let `g, h ∈ F` with reduced forms `g = g_1⋯g_k` and `h = h_1⋯h_n`. Let `r`
be the largest integer `<= min(k,n)` such that `g_(k+1-t) h_t = 1` for all
`1 <= t <= r`. Put

```text
W_r = ψ(g_(k-r+1))⋯ψ(g_k) ψ(h_1)⋯ψ(h_r),
P   = ψ(g_1)⋯ψ(g_(k-r)),        Q = ψ(h_(r+1))⋯ψ(h_n),
```

so that `φ(g)φ(h) = P W_r Q`.

**The cancelled middle is almost the identity.** We show
`d(W_r, id) <= rδ` by induction on `r`. Write
`W_r = ψ(a) W_(r-1) ψ(b)` with `a = g_(k-r+1)` and `b = h_r`. These lie in
`F_j` for one `j ∈ J`, and `ab = 1`. By (H1), (H2) and unitality,

```text
d(W_r, id) <= d(ψ(a) W_(r-1) ψ(b), ψ(a)ψ(b)) + d(ψ(a)ψ(b), ψ(ab))
           =  d(W_(r-1), id) + d(ψ_j(a)ψ_j(b), ψ_j(ab))  <  (r-1)δ + δ.
```

By (H1), `d(φ(g)φ(h), PQ) = d(W_r, id) <= rδ`.

**The junction.** There are two cases.

- *Case (i).* One of the following holds: `r = k`; `r = n`; or `g_(k-r)` and
  `h_(r+1)` lie in different factors. Then
  `g_1⋯g_(k-r) h_(r+1)⋯h_n` is the reduced form of `gh`, so `φ(gh) = PQ`.
- *Case (ii).* `r < min(k,n)`, and `g_(k-r)` and `h_(r+1)` lie in the same
  `G_j`. By maximality of `r`, `u = g_(k-r) h_(r+1) ≠ 1`. The reduced form of
  `gh` is `g_1⋯g_(k-r-1) u h_(r+2)⋯h_n`, because `g_(k-r-1)` and `h_(r+2)`
  do not lie in `G_j`. With `P = P' ψ(g_(k-r))` and `Q = ψ(h_(r+1)) Q'`,
  this gives `φ(gh) = P' ψ_j(u) Q'`. By (H1),
  `d(PQ, φ(gh)) = d(ψ_j(g_(k-r))ψ_j(h_(r+1)), ψ_j(u)) < δ`, since both
  syllables lie in `F_j`.

In both cases `d(φ(gh), φ(g)φ(h)) < (r+1)δ <= (ℓ_max+1)δ < ε` by (FP1). So `φ`
is `(F,ε)`-multiplicative.

## Step 6: good points

Put

```text
S  = { a ∈ A : a ∈ D_j for every j ∈ J, and λ^1(a) ∈ L_inj },
S° = { a ∈ S : ψ(g_t)ψ(g_(t+1))⋯ψ(g_k) a ∈ S  for all g = g_1⋯g_k ∈ F, 1 <= t <= k }.   (FP5)
```

For `a ∈ S`, the following hold.
- `a ∈ S'_1`.
- `β_j(a) = β°_j(a) ∈ S'_j` and `λ^j(β_j a) = λ^1(a)` for every `j ∈ J`,
  by (FP3).

Put `B = B'`, and for `a ∈ S` put `π_a = λ^1(a)|_E : E → B`. It is injective.

**Counting.** By (FP3) and (R4),
`|A \ S| <= Σ_(j∈J) |A \ D_j| + |{ a ∈ S'_1 : λ^1(a) ∉ L_inj }| < (m+1)δN`.

Each of the `Ł` suffix products `w = ψ(g_t)⋯ψ(g_k)` is a permutation of `A`,
so `|{ a : w a ∉ S }| = |A \ S|`. Hence

```text
|A \ S°| <= (1 + Ł) |A \ S| < (1 + Ł)(m + 1) δ N < ε N
```

by (FP1), and `|S°| > (1-ε)|A|`.

## Step 7: orbit approximation

Let `s ∈ S°`, `g = g_1⋯g_k ∈ F` reduced, and `x ∈ E` with `g^-1 x ∈ E`. We show
`λ^1(φ(g)s)(x) = λ^1(s)(g^-1 x)`. When `φ(g)s ∈ S°`, this is
`π_(φ(g)s)(x) = π_s(g^-1 x)`, which is the GKP condition.

Put `s_(k+1) = s` and `s_t = ψ(g_t) s_(t+1)` for `t = k, …, 1`, so
`s_1 = φ(g)s`. By (FP5), every `s_t` lies in `S`. Put
`y_t = (g_1⋯g_(t-1))^-1 x` for `1 <= t <= k+1`. By (FP0), every `y_t` lies in
`E'`. Moreover `y_1 = x`, `y_(k+1) = g^-1 x` and `y_(t+1) = g_t^-1 y_t`.

Fix `t <= k`, and let `j = i_t ∈ J` and `h = g_t ∈ F_j`. Put `b = β_j s_(t+1)`
and `b' = β_j s_t`. Then `b' = β_j ψ_j(h) s_(t+1) = φ'_j(h) b`. Because
`s_t, s_(t+1) ∈ S`, both `b` and `b'` lie in `S'_j`, with
`λ^j(b) = λ^1(s_(t+1))` and `λ^j(b') = λ^1(s_t)`. Apply (R2) with `y = y_t`
and `h^-1 y_t = y_(t+1) ∈ E'`:

```text
λ^1(s_t)(y_t) = λ^j(b')(y_t) = λ^j(b)(y_(t+1)) = λ^1(s_(t+1))(y_(t+1)).      (FP6)
```

Chaining (FP6) over `t = 1, …, k` gives
`λ^1(φ(g)s)(x) = λ^1(s)(g^-1 x)`.

So `φ` is unital, `(F,ε)`-multiplicative, and an `(F,E,ε)`-orbit
approximation of `α`, with good set `S°` and labels `π`. Since `F`, `E` and
`ε` were arbitrary, `α` is sofic. `∎`

## Remarks

- **Where each hypothesis is used.**
  - Soficity of each `α_j` is used only through (FM), on the one packet `E'`.
  - The free-product structure is used twice. Reduced forms make (FP4) well
    defined. The junction analysis in Step 5 sees only one merge.
  - No soficity of the groups `G_i` is used.
- **Why the randomization is needed.** Without the coordinate `T_j`, the
  factor models realize different labelled patterns with different
  frequencies. Then no bijection can match the labels of `A_1` and `A_j` on
  most points. Post-composing with a uniformly random `τ` makes each factor's
  label distribution exactly uniform on `L` (R3). Equal distributions can be
  matched.
- **Countable index sets.** A given `(F,E,ε)` meets only finitely many
  factors, so no appeal to GKP Proposition 2.15(4) is needed.
- **Theorem 2.19 is recovered.** This remark is outside the proof and uses an
  import. A countable free group is `*_(n∈N) Z` or a finite free product of
  copies of `Z`. Every action of `Z` is sofic by GKP Theorem 2.17. See
  [[all-actions-sofic-groups-closed-under-free-products]].
