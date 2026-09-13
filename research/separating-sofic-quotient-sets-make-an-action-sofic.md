---
rg: 2
id: separating-sofic-quotient-sets-make-an-action-sofic
kind: claim
title: Actions separated by maps to sofic actions are sofic, products of sofic actions are sofic, and Mikhailova ropes over residually amenable bases are sofic
distinct_from:
  uas-base-gives-sofic-hnn-coset-action: that proves every action of a LERA group is sofic and applies it to ascending HNN extensions; this is a per-action separation lemma, which needs no hypothesis on the other subgroups of the actor, applied to Mikhailova edges in a product of free groups, which is not LERF.
  co-amenable-induction-of-sofic-actions: that builds models for a single amenable coset space; this pulls labels back from separating quotient sets and says nothing about amenability of the action.
  amenable-base-makes-mikhailova-edge-co-amenable: that concerns an amenable base only; the rope conclusion here holds for every residually amenable base, including residually finite ones and ones with unsolvable word problem.
---

ESTABLISHED (unreviewed). Soficity of an action is GKP Definition 2.1(5).

**(S1) Separation.** Let `α : G ↷ X`. Suppose that for every finite `E <= X`
there are a sofic action `β : G ↷ Y` and a `G`-equivariant map `p : X -> Y`
injective on `E`. Then `α` is sofic.

**(S2) Products.** If `α_i : G_i ↷ X_i` is sofic for `i = 1, 2`, then the
product action `G_1 x G_2 ↷ X_1 x X_2` is sofic.

**(C1) Separable subgroups.** If `K <= G` is an intersection of finite-index
subgroups, then `G ↷ G/K` is sofic.

**(C2) Residually co-amenable-core subgroups.** Suppose `K <= G` is an
intersection of subgroups `K_i` such that each `G / core_G(K_i)` is amenable.
Then `G ↷ G/K` is sofic.

**(C3) Residually amenable Mikhailova ropes.** Let `φ : F ->> Q` with `F`
free, and let `M_Q = { (u,v) : φ(u) = φ(v) } <= F x F`. If `Q` is residually
amenable, the coset action `F x F ↷ (F x F)/M_Q` is sofic. Hence, for every
sofic group `L`, the free wreath product `L wr^*_((F x F)/M_Q) (F x F)` is
sofic. In particular the Mikhailova rope `< F x F, v | [v, M_Q] = 1 >` is
sofic.

DERIVATION [[separating-sofic-quotient-sets-make-an-action-sofic-proof]].

## Reach of (C3)

- It covers amenable `Q`, the design of
  [[amenable-base-makes-mikhailova-edge-co-amenable]]. There the rope is
  sofic, but the reason is not co-amenability of the edge: the action factors
  through the amenable groups `Q_i x Q_i`.
- It covers residually finite `Q`. There the rope is already residually
  finite, since `M_Q` is separable
  ([[centralizing-hnn-is-residually-finite-iff-edge-is-separable]]).
- It covers finitely presented residually amenable `Q` with unsolvable word
  problem, such as the finitely presented solvable groups of Kharlampovich.
  There `M_Q` is not separable and the rope is not residually finite, yet it
  is sofic.
- It does **not** reach the compiler. The compiler's Mikhailova base is the
  Higman host `H_e`. On the `FIN` branch `H_e` contains the nonsofic seed, so it
  is not residually amenable. On the `INF` branch its residual amenability is
  unknown and is not supplied by the Higman construction.
