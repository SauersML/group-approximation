---
rg: 2
id: all-actions-sofic-groups-free-product-closure-proof
kind: route
title: Regular action gives soficity, set induction gives subgroups, the free-product action theorem gives free products
target: all-actions-sofic-groups-closed-under-free-products
requires:
  - free-products-of-sofic-actions-are-sofic
  - gkp-sofic-action-toolkit
  - gkp-amenable-group-actions-are-sofic
  - coordinate-action-not-sofic
  - abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center
artifacts:
  - research/artifacts/free-products-of-sofic-actions-2026-09-16.md
---

The definitions are those of GKP Definition 2.1, as recalled in
`free-products-of-sofic-actions-are-sofic-proof`.

**Isomorphism invariance.** Let `θ : Y → Y'` be a `G`-equivariant bijection.
If `φ` is a unital, `(F,ε)`-multiplicative `(F,θ(E),ε)`-orbit approximation of
`G ↷ Y'` with labels `π_s`, then the same `φ` with labels `π_s ∘ θ` is an
`(F,E,ε)`-orbit approximation of `G ↷ Y`. So soficity of an action depends
only on the isomorphism class of the `G`-set.

## Item 1: members are sofic

Let `G ∈ 𝒜`. Fix finite `F ⊆ G` and `ε > 0`, and put `E = F ∪ {1}`. Apply
Definition 2.1(5) to the left regular action `G ↷ G` with `F`, `E` and `ε`.
This gives a unital, `(F,ε)`-multiplicative `φ` with good set `S`,
`|S| > (1-ε)|A|`, and injective labels `π_s`.

Let `g ∈ F \ {1}` and `s ∈ S`, and suppose `φ(g)s = s`. Take `x = g ∈ E`;
then `g^-1 x = 1 ∈ E` and `φ(g)s ∈ S`. The orbit condition gives
`π_s(g) = π_(φ(g)s)(g) = π_s(1)`, which contradicts injectivity. So `φ(g)` has
no fixed point in `S`, and `d(φ(g), id) >= |S|/|A| > 1-ε`. These are
sofic approximations of `G`.

## Item 2: closure

**Subgroups.** Let `H ≤ G ∈ 𝒜`, and let `H ↷ Y` be an action on a countable
set. Form the induced `G`-set `X = G ×_H Y = (G × Y)/((gh, y) ~ (g, hy))`.
It is countable. The map `ι(y) = [1,y]` is injective, since the class of
`(1,y)` is `{(h, h^-1 y) : h ∈ H}`. It is also `H`-equivariant, since
`h[1,y] = [h,y] = [1,hy]`. So every `H`-orbit `Hy ⊆ Y` is `H`-isomorphic to
the `H`-orbit `ι(Hy)` of `X|_H`.

- `G ↷ X` is sofic because `G ∈ 𝒜`.
- By GKP Proposition 2.15(3) and (2) ([[gkp-sofic-action-toolkit]]), each
  `H`-orbit of `X|_H` carries a sofic action.
- By isomorphism invariance, each `H`-orbit of `Y` carries a sofic action.
- By Proposition 2.16, `H ↷ Y` is sofic.

Hence `H ∈ 𝒜`.

**Increasing unions.** Let `G = ∪_n G_n` with `G_1 ⊆ G_2 ⊆ ⋯` and
`G_n ∈ 𝒜`, and let `G ↷ X` be any action. Its restriction to each `G_n` is
sofic. By Proposition 2.15(4), the action is sofic.

**Free products.** Let `G = *_(i∈I) G_i` with `I` countable and `G_i ∈ 𝒜`,
and let `G ↷ X` be any action. Each restriction to `G_i` is an action of
`G_i`, hence sofic. By [[free-products-of-sofic-actions-are-sofic]], the
action is sofic.

## Item 3: members

Countable amenable groups lie in `𝒜` by GKP Theorem 2.17
([[gkp-amenable-group-actions-are-sofic]]). Item 2 then gives every countable
free product of them. `Z` is amenable, and a countable free group is
`*_(n∈N) Z` or a finite free product of copies of `Z`.

## Item 4: no quotient closure

`coordinate-action-not-sofic` gives a countable group `G` with a nonsofic
action `G ↷ G/Γ`, so `G ∉ 𝒜`. Every countable group is a quotient of the free
group `F_∞` on a countable generating set, and `F_∞ ∈ 𝒜` by item 3.

If `L ⊇ G` is countable and `L ∈ 𝒜`, then subgroup closure gives `G ∈ 𝒜`,
which is false. So no countable group containing `G` lies in `𝒜`.

## Item 5: the group `Γ_p * Z`

By `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`, `Γ_p` is
finitely presented and amenable, with a central element `c_p ≠ 1` of order
`p` that is killed by every finite-dimensional unitary representation (APQ1).

- **Membership.** `Γ_p ∈ 𝒜` and `Z ∈ 𝒜` by item 3, so `Γ_p * Z ∈ 𝒜` by
  item 2.
- **Finite presentation.** Concatenating finite presentations of the two
  factors gives one for the free product.
- **Nonamenability.** Pick `c ∈ Γ_p \ {1}`, let `t` generate `Z`, and put
  `u = t` and `v = c t c^-1`. Take a nonempty reduced word in `u` and `v`
  with nonzero exponents. Substituting `v^m = c t^m c^-1` gives a product
  such as `t^(n_1) c t^(m_1) c^-1 t^(n_2) ⋯`. Its syllables alternate between
  nonzero powers of `t` and the elements `c^(±1) ∈ Γ_p \ {1}`, so it is
  already a reduced free-product word. Hence it is nontrivial, and
  `⟨u, v⟩ ≅ F_2`.
- **Torsion.** `c_p` has order `p`, so the group is not free.
- **Not residually finite.** Let `q : Γ_p → Q` be a homomorphism to a finite
  group, and compose it with the faithful left regular representation
  `Q → U(|Q|)`. By (APQ1), `q(c_p) = 1`. So `Γ_p` is not residually finite.
  Residual finiteness passes to subgroups, so `Γ_p * Z` is not residually
  finite either.
- **Not LERF.** LERF implies residual finiteness, since the trivial subgroup
  is separable.
- **Not a proper increasing union.** A finitely generated group that is the
  union of an increasing chain equals some member of the chain.

`∎`
