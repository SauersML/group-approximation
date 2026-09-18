---
rg: 2
id: abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q-proof
kind: route
title: Direct computation in the abelian base of the wreath product
target: abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q
requires: []
---

Direct proof. Not independently reviewed. Notation as in the claim. Write the
abelian base `B = ⊕_X A` additively. For `h ∈ W` and `w ∈ B`,
`h w h^-1 = π(h)·w`, the permutation action of `π(h)` on finitely supported
functions, because `B` is abelian.

## Lemma 1 (monic relations force finite order)

Let `h ∈ W` and `0 ≠ w ∈ B`. Suppose `p(π(h))·w = 0` for a Laurent polynomial
`p ∈ Z[t^{±1}]` whose highest-degree coefficient is `±1`. Then `π(h)` has
finite order.

*Proof.* Suppose `g = π(h)` has infinite order. A point stabilizer of `⟨g⟩` is a
finite subgroup of an infinite cyclic group, so it is trivial, and `⟨g⟩` acts
freely on `X`. Choosing one point in each `⟨g⟩`-orbit identifies `B`, as a
`Z[t^{±1}]`-module with `t` acting as `g`, with `⊕_orbits A[t^{±1}]`. On each
summand multiplication by `p` is injective: if `f ≠ 0` has highest-degree term
`a t^N` with `a ≠ 0`, then `p f` has highest-degree term `±a t^{N+M}`, where
`M` is the degree of `p`. So `p(g)·w = 0` forces `w = 0`, a contradiction. ∎

## Lemma 2 (roots in torsion-free nilpotent groups)

In a torsion-free nilpotent group `N`, `a^r = b^r` with `r >= 1` implies `a = b`.
Hence `[x^r, y] = 1` implies `[x, y] = 1`.

*Proof.* Standard (Mal'cev). Induct on the class `c` of `⟨a, b⟩`. If `c <= 1`,
then `(a b^-1)^r = 1`, so `a = b` by torsion-freeness. If `c >= 2`, then
`b^-1 a b` and `a` have the same `r`-th power `b^-1 a^r b = b^r = a^r`, and both
lie in `M = ⟨a⟩ γ_2(⟨a,b⟩)`. From `[⟨a⟩γ_2, ⟨a⟩γ_2] ⊆ γ_3` and induction,
`γ_i(M) ⊆ γ_{i+1}(⟨a,b⟩)`, so `M` has class at most `c - 1`. By induction
`b^-1 a b = a`. Then `a, b` commute, `(a b^-1)^r = 1`, and `a = b`. For the
second sentence, `(y x y^-1)^r = y x^r y^-1 = x^r`, so `y x y^-1 = x`. ∎

## Part 1 (nonabelian torsion-free nilpotent H)

Let `K = H ∩ B`, an abelian normal subgroup of `H`, and suppose `K ≠ 1`. Let `c`
be the class of `H`. For `h ∈ H` and `w ∈ K`, in additive notation
`(π(h) - 1)·w = h w h^-1 - w` is the commutator `[h, w]`, so
`(π(h) - 1)^c · w = 0` because `γ_{c+1}(H) = 1`. Take `w ≠ 0` in `K`. The
polynomial `(t - 1)^c` is monic, so by Lemma 1 every `π(h)`, `h ∈ H`, has finite
order. As `ker(π|_H) = K`, the group `H/K` is torsion.

Now let `h ∈ H`, `k ∈ K`. Some `h^r ∈ K` with `r >= 1`, and `K` is abelian, so
`[h^r, k] = 1`, and `[h, k] = 1` by Lemma 2. Thus `K ⊆ Z(H)`. For any
`g, h ∈ H`, some `g^s ∈ K ⊆ Z(H)`, so `[g^s, h] = 1` and `[g, h] = 1` by Lemma 2.
So `H` is abelian, a contradiction. Hence `K = 1`. ∎

## Part 2 (H ≅ Aff(Q))

Write elements of `Aff(Q)` as `x -> λx + μ` (`λ ∈ Q^x`, `μ ∈ Q`), with
translations `τ_μ` and the dilation `δ : x -> 2x`, so `δ τ_μ δ^-1 = τ_{2μ}`.
Let `K = H ∩ B`, an abelian normal subgroup of `H`.

*K consists of translations.* If `g : x -> λx + μ` lies in `K` with `λ ≠ 1`,
then for `ν ≠ 0` the element `τ_ν g τ_ν^-1 g^-1` is the translation by
`ν(1 - λ) ≠ 0` and lies in `K`, since `K` is normal. But `g τ_{ν(1-λ)} g^-1` is
the translation by `λν(1-λ)`, which differs from `τ_{ν(1-λ)}`, so `K` is not
abelian. Hence every element of `K` is a translation.

*K = 1.* Suppose `0 ≠ w = τ_μ ∈ K`. Then `π(δ)·w = δ w δ^-1 = τ_{2μ} = 2w`, so
`(π(δ) - 2)·w = 0` with the monic polynomial `t - 2`. By Lemma 1, `π(δ)` has
finite order `r >= 1`, so `δ^r ∈ ker(π|_H) = K`. But `δ^r : x -> 2^r x` is not
a translation, a contradiction. Hence `K = 1`. ∎

## Where it is sharp

- Abelian `H` can sit in the base: `(Q,+) <= ⊕_X Q`.
- Finite stabilizers are used only in Lemma 1. With an infinite point stabilizer
  containing an infinite-order `g`, a fixed lamp `w` gives `(π(g)-1)·w = 0`, and
  the argument stops. This is the setting of
  `pbh-closed-under-permutational-wreaths-with-infinite-stabilizers`.
- Nonabelian lamps are not covered.
