---
rg: 2
id: llosa-isenrich-weis-dehn-bound-for-cocompact-actions
kind: claim
title: "Llosa Isenrich–Weis: Dehn function upper bounds for cocompact actions on trees and on complexes with finite-index face stabilizers"
---

Imported from Claudio Llosa Isenrich and Jannis Weis, *A Brown Theorem for
Dehn functions of graphs of groups*, arXiv:2608.07191v1 (7 August 2026), p. 2,
verbatim:

> **Theorem B.** Let `G` be a group that acts cellularly and cocompactly
> without inversion on a tree `T`. Assume that all vertex stabilizers `G_v` are
> finitely presented and that all edge stabilizers `G_e` are finitely
> generated. Then `δ_G(n) ≼ n · max_{v ∈ V(T)} δ_{G_v}( edist_T‾(n) )`, where
> `edist_T(n) = max_{e ∈ E(T)} dist^G_{G_e}(n)`.

> **Theorem C.** Let `G` be a group that acts cellularly and cocompactly
> without inversion on a simply connected simplicial complex `X`. Assume that
> all vertex stabilizers `G_v` are finitely presented, that all edge
> stabilizers `G_e` are finitely generated, and that `[G_e : G_σ] < ∞` for all
> 2-cells `σ` and edges `e ⊂ σ`. Then
> `δ_G(n) ≼ δ_X(n) · max_{v ∈ X^(0)} δ_{G_v}( edist_X‾( δ_X(n) ) )`, where
> `edist_X(n) = max_e dist^G_{G_e}(n)` and `e` runs over all edges of `X`.

Conventions (p. 3–4): `f ≼ g` if `f(n) ≤ C g(Cn + C) + Cn + C` for some
`C > 0`; `f‾` is the superadditive closure;
`dist^G_H(n) = max { ℓ_H(h) : h ∈ H, ℓ_G(h) ≤ n }` (Definition 2.1); `δ_X` is
the Dehn function of the complex (Definition 2.3).

From the same page: the form of Theorem B is sharp in general, since
`BS(1,2)` is an HNN extension with exponentially distorted infinite cyclic
edge and vertex stabilizers and exponential Dehn function; and "A version of
the question whether such an analogue exists for the first Dehn function
`δ^1_G` was raised by Zaremsky [Zar26, Problem 1.17]. We give an affirmative
answer if `X` is 1-dimensional." The paper also proves higher-dimensional
analogues for trees (Theorem D, Corollary E). It cites Sauer–Weis [SW26] for a
polynomial upper bound for complexes of groups, assuming polynomial bounds on
the filling functions of the complex, the homological Dehn functions of all
cell stabilizers and the distortion of cell stabilizers.

This partly answers Zaremsky Problem 1.17
(`zaremsky-1-17-dehn-function-from-cocompact-action-data`) but does not
establish its root: the general case without `[G_e : G_σ] < ∞` is open.
