---
rg: 2
id: twisted-btb-clopen-action-is-type-a
kind: claim
title: A finitely presented twisted Brin-Thompson group acts with type (A) on the proper clopen subsets of its Cantor cube
distinct_from:
  fp-full-binary-cantor-groups-have-type-a-actions: that is the clopen action of a finitely presented full group containing standard V on binary Cantor space; this is the clopen action of a twisted Brin-Thompson group on the Cantor cube C^S, whose elements permute coordinates, and it is proved from the brick calculus rather than from the fullness hypothesis of that claim.
  twisted-brin-thompson-finite-presentation-criterion: that decides when SV_G is finitely presented from the action of G on S; this takes that finite presentation as input and produces a second, oligomorphic action of SV_G itself, with point stabilizers isomorphic to SV_G x SV_G.
  type-a-actions-closed-under-products-and-finite-wreaths: that builds type (A) actions of products and finite wreaths from given type (A) actions; this produces a type (A) action of a twisted Brin-Thompson group on a new set, the clopen subsets of its cube.
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

**ESTABLISHED** by `twisted-btb-clopen-action-type-a-proof`.

**Setting** (Belk--Zaremsky brick calculus, as used in
`regular-cyclic-twisted-core-proof`). Let a group `G` act faithfully on a
countable set `S` with type (A) in the sense of
`type-a-action-gives-boone-higman-for-subgroups`.
- `C = {0,1}^N` and `C^S` is the Cantor cube.
- A **brick** is `B(u) = {κ : κ(s) has prefix u(s) for all s}` for a finitely
  supported `u : S -> {0,1}^*`. Write `h_u : C^S -> B(u)` for prefix insertion.
- `τ_g` is the coordinate permutation `(τ_g κ)(s) = κ(g^-1 s)`.
- `SV_G` is the group of homeomorphisms `f` of `C^S` for which there are brick
  partitions `{B(u_i)}` and `{B(v_i)}` of `C^S` and `g_i in G` with
  `f = h_(v_i) τ_(g_i) h_(u_i)^-1` on `B(u_i)`. Each such piece is a **branch**.

Let `Ω` be the countable set of proper nonempty clopen subsets of `C^S`.

**Claim.** The action of `SV_G` on `Ω` is of type (A):
1. `SV_G` is finitely presented;
2. the action is faithful;
3. two `k`-tuples in `Ω` lie in one orbit exactly when they have the same
   pattern of nonempty Boolean atoms, so there are finitely many orbits on
   `k`-tuples for every `k`: seven on ordered pairs (counting pairs `(U,U)`),
   five on two-element subsets;
4. the stabilizer of `U in Ω` is `D(U) x D(U^c)`, where `D(X)` is the subgroup
   of elements supported in `X`, and each factor is isomorphic to `SV_G`. In
   particular point stabilizers are finitely presented.

No hypothesis beyond the type (A) action of `G` is used. The consumer is
`a2-action-with-non-finitely-presented-image`, where a diagonal copy of
Thompson's group `V` normalizes this action.
