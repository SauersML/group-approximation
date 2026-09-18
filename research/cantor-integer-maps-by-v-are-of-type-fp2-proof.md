---
rg: 2
id: cantor-integer-maps-by-v-are-of-type-fp2-proof
kind: route
title: "C(C,L) ⋊ V is the one-point abstract twisted Brin–Thompson group of L, and the trivial action on a point has type [A_2] or [HA_2] exactly when L is finitely presented or of type FP_2"
target: cantor-integer-maps-by-v-are-of-type-fp2
requires:
  - abstract-btb-pairs-fp-and-relatively-simple
  - ha2-actions-give-fp2-twisted-brin-thompson-groups
  - v-times-shift-fp2-forces-fp2-of-every-subshift-restriction
---

## Imported text

Source: F. Fournier-Facio, X. Wu, M. C. B. Zaremsky, *Abstract twisted
Brin–Thompson groups*, arXiv:2603.24687v2. Fetched on 2026-09-18 from the arXiv
HTML; the quotations below were returned verbatim.

- (Q1) "if S={s} is a single point, so G↷{s} is trivial, then {s}V_G is the
  labeled Thompson group V(G); this was essentially introduced by Thompson in
  [Tho80], and see also [WWZZ25, Subsection 1.5] for a more modern treatment."
- (Q2) Expansion: "The k-th expansion with color s∈S of (F₋,σ,(g₁,…,gₙ),F₊) is
  ((F₋)_{σ(k)}^{(s)g_k},(σ)ς_k^n,(g₁,…,g_{k-1},g_k,g_k,g_{k+1},…,g_n),(F₊)_k^s)."
- (Q3) Multiplication:
  "[F₋,σ,(g₁,…,gₙ),F₊][E₋,τ,(h₁,…,hₙ),E₊]:=[F₋,στ,(g_{τ(1)}h₁,…,g_{τ(n)}h_n),E₊]."
- (Q4) Definition 2.12: "The abstract twisted Brin–Thompson group SV_G is the
  subgroup of S𝒱_G consisting of elements with rank and corank 1."

The finiteness theorems come from established imports:
- FFWZ Theorem 4.1(ii), through `abstract-btb-pairs-fp-and-relatively-simple`:
  `SV_G` "is finitely presented if and only if G ↷ S is of type [A_2]". Type
  [A_2] means `G` is finitely presented, point stabilizers are finitely
  generated, and there are finitely many orbits on `S × S`.
- FFWZ Corollary 4.14, through `ha2-actions-give-fp2-twisted-brin-thompson-groups`:
  "If G↷S is of type [HA_2] then SV_G is of type FP_2."

## Step 1. The one-point group is C(C, L) ⋊ V

Let `S = {s}`. There is one colour and `(s)g = s`, so the forests in (Q2) are
ordinary binary forests, and by (Q4) the elements have single trees at both ends.

Take an element `x = [T₋, σ, (g_1,…,g_n), T₊]`. Let `u_1,…,u_n` be the leaf
addresses of `T₊` and `v_1,…,v_n` those of `T₋`. Define:
- `h_x ∈ V` by `u_i w ↦ v_{σ(i)} w`;
- `λ_x ∈ C(C, L)` by `λ_x = g_i` on the cylinder `[u_i]`.

**Well defined.** By (Q2), the k-th expansion splits leaf `k` of `T₊` and leaf
`σ(k)` of `T₋` compatibly, and it copies `g_k` to both children. Neither
`h_x` nor `λ_x` changes.

**Homomorphism.** In (Q3), `E₋ = F₊` after expansion. The product sends leaf
`i` of `E₊` to leaf `τ(i)` of `F₊`, then to leaf `στ(i)` of `F₋`, with label
`g_{τ(i)} h_i`. So `h_{xy} = h_x h_y` and `λ_{xy} = (λ_x ∘ h_y) · λ_y`. This is
the multiplication of `C(C, L) ⋊ V`, with `V` acting by precomposition, written
as a right action. The left form `k·μ = μ ∘ k^{-1}` gives an isomorphic group.

**Onto.** Take `(λ, h)`. Choose a finite cylinder partition of `C` that refines
the level sets of `λ` and on whose pieces `h` is a prefix replacement. Refine it
by expanding so that it is the set of leaves of a tree `T₊`. The image
cylinders form a complete prefix code, hence the leaves of a tree `T₋`. Reading
off `σ` and the constant values of `λ` gives a preimage.

**Injective.** Two representatives of elements with the same `(λ, h)` can be
expanded to a common `T₊`. Then `h` determines `T₋` and `σ`, and `λ` determines
the labels. So the representatives agree after expansion. In particular
`(1, id)` has only the representatives `[T, id, (1,…,1), T]`, which are the
identity by (Q3).

So `{s}V_L ≅ C(C, L) ⋊ V`. This agrees with (Q1) and with the identification
recorded in `labelled-thompson-groups-are-acyclic`.

## Step 2. Finiteness

The trivial action `L ↷ {s}` has point stabilizer `L` and a single orbit on
`{s} × {s}`.
- If `L` is finitely presented, then `L` is finitely generated and the action
  is of type [A_2]. Theorem 4.1(ii) makes `C(C, L) ⋊ V` finitely presented.
- If `L` is of type FP_2, then `L` is finitely generated and the action is of
  type [HA_2]. Corollary 4.14 makes `C(C, L) ⋊ V` of type FP_2.

This proves item 1. For item 2 take `L = Z`, which is finitely presented, and
use the fact that finitely presented groups are of type FP_2.

## Step 3. The fixed-point test

Step 4 of `v-times-shift-fp2-forces-fp2-of-every-subshift-restriction-proof`
proves:
- the restriction of `G = G_V × (Z ⋉ Σ)` to `C × {0^Z}` is `G_V × Z`;
- its full group is `C(C, Z) ⋊ V` with `V` acting by precomposition;
- that full group is the image of `A(G)` under restriction.

By Step 2 that group is finitely presented. So item 2 of
`v-times-shift-fp2-forces-fp2-of-every-subshift-restriction` is true, which
proves item 3. ∎

## Trust surface

- (Q1)–(Q4) were read as fetched quotations, not from the PDF.
- The meaning of "rank and corank 1" as single trees is inferred from the
  definition.
- The proofs of FFWZ Theorem 4.1 and Corollary 4.14 were not re-read.
