---
rg: 2
id: g-x-free-set-actions-sofic-when-kernel-amenably-separable-proof
kind: route
title: Følner-times-free product models, then separate points by amenable quotients of the first factor
target: g-x-free-set-actions-sofic-when-kernel-amenably-separable
requires:
  - separating-sofic-quotient-sets-make-an-action-sofic
  - gkp-free-group-actions-are-sofic
  - gkp-sofic-action-toolkit
---

GKP Definition 2.1(3), verbatim from arXiv:2401.04945v3 p. 3: `φ : G -> Sym(A)`
is an `(F,E,ε)`-orbit approximation of `α` if there are a finite set `B` and
`S <= A` with `|S| > (1-ε)|A|`, and for each `s in S` an injective
`π_s : E -> B` with `π_(φ(g)s)(x) = π_s(α(g^-1)x)` for all `s in S`, `g in F`,
`x in E`, whenever `φ(g)s in S` and `α(g^-1)x in E`. Normalized Hamming
distance on `Sym(Φ x B)` satisfies
`d(σ x ψ, σ' x ψ') <= d(σ,σ') + d(ψ,ψ')`.

## (A) Amenable-quotient factor

Let `q : G_1 -> K = G_1/M`. Since `M x 1` acts trivially, `K` acts on `X`;
write `k.x = α(k̃,1)x` for any lift `k̃`. Fix finite `F <= G_1 x H`, `E <= X`
and `ε > 0`. Let `F_1`, `F_2` be the coordinate projections of `F` together
with `1`, `F_K = q(F_1) ∪ q(F_1)^-1`, `F_K' = F_K F_K`, and choose `δ > 0` with
`(|F_K| + 5) δ < ε`.

*Følner model.* `K` is amenable, so there is a finite `Φ <= K` with
`|Φ △ kΦ| < 2δ|Φ|` for `k in F_K'`. For `k in K` let `σ(k) in Sym(Φ)` be
any bijection with `σ(k)k_0 = k k_0` whenever `k_0, k k_0 in Φ`, and
`σ(1) = id`. As in the proof of GKP Theorem 2.17 (p. 9), `σ ∘ q` is unital and
`|Φ| d(σ(k)σ(k'), σ(kk')) <= |Φ △ k'^-1 Φ| + |Φ △ (kk')^-1 Φ| < 4δ|Φ|` for
`k, k' in F_K`, because `k'^-1` and `(kk')^-1` lie in `F_K'`. Put
`Φ_0 = ∩_(k in F_K) (Φ ∩ k^-1 Φ)`. Then `|Φ_0| > (1 - |F_K|δ)|Φ|`, and
`σ(k)k_0 = k k_0` for `k in F_K`, `k_0 in Φ_0`.

*Free-factor model.* Put `E_H = Φ^-1 . E = { k_0^-1 . x : k_0 in Φ, x in E }`,
a finite set. As `α|_H` is sofic, choose `ψ : H -> Sym(B)` unital,
`(F_2, δ)`-multiplicative, and an `(F_2, E_H, δ)`-orbit approximation with
good set `S_B` and labels `π^H_t : E_H -> C`.

*Product.* Let `A = Φ x B` and `φ(g_1,h) = σ(q(g_1)) x ψ(h)`. It is unital.
The two coordinates act on different factors of `A`, so
`d(φ(g)φ(g'), φ(gg')) < 4δ + δ < ε` for `g, g' in F`. Put `S = Φ_0 x S_B`, so
`|S|/|A| > (1 - |F_K|δ)(1-δ) > 1 - ε`. For `s = (k_0,t) in S` and `x in E` set

```text
π_s(x) = π^H_t(k_0^-1 . x).
```

This is injective, since `x -> k_0^-1 . x` is a bijection of `X` into `E_H` on
`E`, and `π^H_t` is injective on `E_H`.

*Equivariance.* Let `g = (g_1,h) in F`, `k = q(g_1)`, `s = (k_0,t) in S`,
`x in E`, with `φ(g)s in S` and `α(g^-1)x in E`. Since `k_0 in Φ_0`,
`φ(g)s = (k k_0, ψ(h)t)` with `k k_0 in Φ`. Put `z = (k k_0)^-1 . x`, which lies
in `E_H`. The actions of `G_1` and `H` commute, so

```text
α(1,h^-1) z = k_0^-1 . ( α(g^-1) x ) in Φ^-1 . E = E_H.
```

Also `t` and `ψ(h)t` lie in `S_B`, and `h in F_2`. The orbit approximation `ψ`
gives

```text
π_(φ(g)s)(x) = π^H_(ψ(h)t)(z) = π^H_t(α(1,h^-1) z)
             = π^H_t(k_0^-1 . α(g^-1)x) = π_s(α(g^-1)x).
```

So `φ` is a unital, `(F,ε)`-multiplicative, `(F,E,ε)`-orbit approximation, and
`α` is sofic. `∎`

## (B) Theorem

Let `X = (G_1 x F)/L` and `N = { a : (a,1) in L }`.

*Step 1: separating one pair.* Let `u = (c,d) in G_1 x F` with `u ∉ L`. We claim
that some `M ⊴ G_1` with amenable quotient has `u ∉ L(M x 1)`. Here
`L(M x 1)` is a subgroup, because `M x 1` is normal, and its second
projection equals `p_2(L)`. If `d ∉ p_2(L)`, take `M = G_1`. Otherwise pick
`a` with `(a,d) in L`. If `(x,d) in L` then `(a^-1 x, 1) in L`, so
`{ x : (x,d) in L } = aN`, and hence `(x,d) in L(M x 1)` iff `x in aNM`. Since
`u ∉ L`, `a^-1 c ∉ N`. Amenable separability gives `M` with `a^-1 c ∉ NM`,
that is `c ∉ aNM`, and so `u ∉ L(M x 1)`.

*Step 2: separating a finite set.* Let `E <= X` be finite. For each of the
finitely many pairs `xL ≠ yL` in `E`, Step 1 applied to `u = x^-1 y` gives an
`M_(x,y)`. Let `M` be their intersection. `G_1/M` embeds into the finite
product of the `G_1/M_(x,y)`, so it is amenable, and `x^-1 y ∉ L(M x 1)` for
each pair. So the natural equivariant map

```text
p : X = (G_1 x F)/L  ->  Y = (G_1 x F)/L(M x 1)
```

is injective on `E`.

*Step 3: `Y` is sofic.* The normal subgroup `M x 1` lies in `L(M x 1)`, so it
fixes every coset: `(m,1) g L(M x 1) = g (g^-1 (m,1) g) L(M x 1) = g L(M x 1)`.
The restriction of `Y` to `1 x F` is an action of a free group, hence sofic by
GKP Theorem 2.19 ([[gkp-free-group-actions-are-sofic]]). By (A), `Y` is sofic.

*Step 4.* By (S1) of [[separating-sofic-quotient-sets-make-an-action-sofic]],
`X` is sofic. `∎`

The same proof works for any countable second factor all of whose actions on
countable sets are sofic, since Step 3 uses nothing else about `F`.

## Consequences (derivations)

1. Apply (B) to the orbit of a point with stabilizer `L`, in either factor
   order. Soficity is orbitwise by GKP Propositions 2.15(2) and 2.16
   ([[gkp-sofic-action-toolkit]]).
2. If `F x 1` acts freely on the orbit, `L ∩ (F x 1) = 1`. The free group `F`
   is residually finite, so `{1}` is an intersection of finite-index normal
   subgroups, and finite groups are amenable.
3. `(a,1)` fixes a point iff `ρ_1(a)` does, iff `ρ_1(a) = 1`, because `P_1`
   acts freely. So `L ∩ (F x 1) = ker ρ_1`. For `a ∉ ker ρ_1`, residual
   amenability of `ρ_1(F) ≅ F/ker ρ_1` gives a normal `M ⊇ ker ρ_1` with
   amenable quotient and `a ∉ M = (ker ρ_1)M`.
4. In `(G x G)/ΔΓ` the subgroup `G x 1` acts freely: `(g,1)(a,b)ΔΓ = (a,b)ΔΓ`
   forces `(a^-1 g a, 1) in ΔΓ`, so `g = 1`. The Kun–Thom `G` is residually
   finite, hence so is `φ_1(F) <= G`. Apply (3).
5. With `N_1 = L ∩ (F x 1)` normal in `F` and `F/N_1` residually amenable,
   argue as in (3).
