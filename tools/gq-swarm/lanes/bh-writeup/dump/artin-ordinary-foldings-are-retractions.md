---
rg: 2
id: artin-ordinary-foldings-are-retractions
kind: claim
title: A folding of the generators of an Artin group onto a standard parabolic subgroup that respects every edge is a retraction; every cyclic standard parabolic subgroup is a retract via the length homomorphism
distinct_from:
  artin-pbh-reduces-to-odd-component-cliques: that uses only the even-boundary retractions (kill every generator outside Λ), which need every edge leaving Λ to be even; this allows generators outside Λ to be sent to generators of Λ, so odd edges may leave Λ. In particular it gives a retraction onto every cyclic parabolic subgroup, which that node's Scope (S1) does not use.
  pbh-class-closed-under-common-retract-amalgams: that is the closure theorem for amalgams over common retracts; this supplies retractions of Artin groups for it to act on.
---

**ESTABLISHED** (route `artin-ordinary-foldings-are-retractions-proof`; lane proof, elementary, not independently reviewed). No priority is claimed: these maps are the "ordinary retractions" of Cisneros de la Cruz--Cumplido--Foniqi--Paris, arXiv:2603.15314 (classification of Artin groups retracting onto all parabolic subgroups; read only through the arXiv HTML summary of its Theorems 1.1--1.3), and the length homomorphism is classical. The proof below is self-contained.

## Setting

`Γ` is a finite simplicial graph, every edge `xy` carries a label `m_xy ∈ {2, 3, 4, ...}`, a non-edge means `m = ∞`, and `A_Γ = < V | Π(x,y;m_xy) = Π(y,x;m_xy) for every edge xy >`, where `Π(x,y;m)` is the alternating word `x y x ⋯` of length `m`. For `Λ ⊆ V`, `A_Λ` is the Artin group of the induced labelled subgraph `Γ[Λ]`.

## Statement

Let `Λ ⊆ V` and let `f : V → Λ ∪ {1}` with `f(z) = z` for every `z ∈ Λ`. Suppose every edge `xy` of `Γ`, with label `m`, satisfies one of:
- (a) `f(x) = f(y)` (both `1`, or the same vertex of `Λ`);
- (b) one of `f(x), f(y)` is `1`, the other is a vertex of `Λ`, and `m` is even;
- (c) `f(x) = z` and `f(y) = z'` are distinct vertices of `Λ`, joined by an edge of `Γ[Λ]` whose label `m_zz'` divides `m`.

Then `x ↦ f(x)` defines a homomorphism `ρ_f : A_Γ → A_Λ` that is the identity on the image of `A_Λ`. So the natural map `A_Λ → A_Γ` is injective and `A_Λ` is a retract of `A_Γ`.

**Cyclic parabolics.** For every vertex `v`, the constant folding `f ≡ v` satisfies (a) on every edge. So `λ_v : A_Γ → <v> ≅ Z`, sending every generator to `v`, is a retraction onto the infinite cyclic subgroup `<v>`. This holds for all labels.

**Even-boundary retractions** (Lemma 5.1 of `research/artifacts/bh-common-retract-amalgams-even-artin-2026-09-16.md`) are the case `f(V \ Λ) = {1}`.

## Example

In `A(A_3) = <u, w, x | uwu = wuw, uxu = xux, wx = xw>`, the folding `x ↦ w` satisfies (c) on `ux` (label 3, and `m_uw = 3` divides 3) and (a) on `wx`. So the dihedral parabolic `<u, w> ≅ A(A_2)` is a retract of `A(A_3)`. (By contrast `<w, x> ≅ Z^2` is not, since `A(A_3)^ab = Z`; see Scope (S1) of the artifact above.)
