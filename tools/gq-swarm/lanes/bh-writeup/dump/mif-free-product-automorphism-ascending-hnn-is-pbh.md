---
rg: 2
id: mif-free-product-automorphism-ascending-hnn-is-pbh
kind: claim
title: For a finitely presented simple MIF group M, every ascending HNN extension along an arbitrary automorphism of M * F_m lies in the permutational Boone--Higman class
distinct_from:
  pbh-class-closed-under-relative-holomorphs: that allows any finitely generated base in the class but only automorphisms of M * F_m that restrict on M to a conjugation; this needs a finitely presented simple MIF base but allows every automorphism of M * F_m, including those restricting to outer automorphisms of M.
  stable-permutation-hnn-of-type-a-actor-is-type-a: that is the abstract statement about one extra permutation normalizing an actor; this applies its mapping-torus case to the BFFHZ actor and a hat automorphism, and adds the free-product normal form and Kurosh step that reach groups not inside the actor.
  relative-automorphism-of-fp-simple-mif-group-has-type-a-action: that is BFFHZ Theorem E, an actor for Aut_M(M * F_n); this is a permanence statement for mapping tori and ascending HNN extensions of subgroups of M * F_m, which are not subgroups of that actor when the automorphism moves M.
  bh-embeddability-survives-decidable-edge-hnn: that is the open HNN permanence with arbitrary finitely generated decidable edges; this settles only the ascending case whose endomorphism is the restriction of an automorphism of M * F_m, for an MIF simple M.
  power-map-free-mapping-tori-satisfy-permutational-boone-higman: that treats power-map endomorphisms of free groups through an affine model; this treats automorphism-induced endomorphisms of subgroups of M * F_m through the BFFHZ actor, and contains no free-group power maps.
---

**ESTABLISHED** through `mif-free-product-ascending-hnn-pbh-proof`. Not
independently reviewed. No priority is claimed.

## Statement

`B_A` is the class of groups that embed in a group admitting an action of type
(A), as in `boone-higman-type-a-class-closed-under-finite-extensions`. MIF means
mixed-identity-free, as in BFFHZ, arXiv:2503.21882v2.

Let `M` be a finitely presented simple MIF group, let `m >= 0`, put
`Q = M * F_m`, and let `β ∈ Aut(Q)` be **arbitrary**. Let `J <= Q` be a subgroup
with `β(J) ⊆ J`, and let

```text
J *_β = < J, t | t j t^-1 = β(j)  (j ∈ J) >
```

be the ascending HNN extension. Then `J *_β ∈ B_A`. In particular:

1. **Mapping tori of M.** `M ⋊_α Z ∈ B_A` for every `α ∈ Aut(M)`, of finite or
   infinite outer order.
2. **Mapping tori of M * F_m.** `(M * F_m) ⋊_β Z ∈ B_A` for every
   `β ∈ Aut(M * F_m)`.
3. **Envelopes.** If `J` is finitely generated, `J *_β` has solvable word problem
   and embeds in a finitely presented simple group, by
   `type-a-action-gives-boone-higman-for-subgroups`.

## The mechanism in one paragraph

By Kurosh, `β` carries `M` to a conjugate of `M`, so after an inner correction
`β = c_g ∘ θ ∘ hat(α)`, where `α ∈ Aut(M)`, `hat(α)` is `α` on `M` and the
identity on the free letters, and `θ` fixes `M` pointwise. Put `P = Q * <x>` and
`Ω = Aut_M(P)`. Right multiplication of `x` by elements of `Q` embeds `Q` in `Ω`,
and `θ` extends to `Ω`. Only `hat(α)` leaves `Ω`. But `hat(α)` normalizes `Ω`,
and on the BFFHZ set `Hom_M(P, M)` it is realized by the permutation
`f -> α ∘ f ∘ hat(α)^-1`, which normalizes the action of `Ω`. So the mapping-torus
case of `stable-permutation-hnn-of-type-a-actor-is-type-a` puts `Ω ⋊ <hat(α)>`
in `B_A`, and `Q ⋊_β Z` embeds in it.

## What is new, and what is not

- **Finite outer order is not new.** If the automorphism `α = β₀|_M` of Step 1 of
  the route has finite order `k` in `Out(M)`, then `β₀^k` restricts on `M` to a
  conjugation. So `Q ⋊_(β₀^k) Z ∈ B_A` by (T) of
  `pbh-class-closed-under-relative-holomorphs`, with base `M ∈ B_A` from BFFHZ
  Theorem C (`fp-simple-highly-transitive-groups-satisfy-pbh`). It has index `k`
  in `Q ⋊_(β₀) Z`, and `B_A` is closed under finite-index overgroups. The new
  content is the case where `α` has infinite order in `Out(M)`.
- **Examples not checked.** This node does not exhibit a finitely presented
  simple MIF group with an automorphism of infinite outer order. BFFHZ (Remark
  3.5, as retrieved from arXiv HTML on 2026-09-16) list finitely presented simple
  Burger--Mozes groups and finitely presented commutator subgroups of
  Röver--Nekrashevych groups as highly transitive and MIF. The graph also has
  `fp-simple-kac-moody-lattices-are-mif` and `binary-leavitt-unit-group-is-mif`.
  Whether any of these has an automorphism of infinite outer order was not
  examined. For an `M` whose `Out(M)` is a torsion group, every instance is
  already covered by the previous bullet.
- **Overlap with an in-flight lane.** On 2026-09-16 the uncommitted artifact
  `research/artifacts/outer-extensions-mif-pbh-2026-09-16.md`, from another
  lane, argues that for `M` finitely presented simple MIF and
  `Inn(M) <= B <= Aut(M)` with `B/Inn(M)` finitely presented, `B ∈ B_A`. With
  `B = < Inn(M), α >` this gives case 1 when `α` has infinite outer order. It
  also gives case 2. Let `θ'` be `θ` on `Q` and the identity on `B`. Then
  `β' = θ' ∘ (c_α on B, identity on F_m)` restricts on `B` to conjugation by
  `α ∈ B`, so (T) with base `B` applies to `B * F_m`. `β'` preserves `Q` and
  restricts there to `β₀`. The route here does not depend on that artifact. It
  uses no kernel computation and no word-map lemma, only the normalizing
  permutation.

## Where it stops

- **Base.** `M` itself must be finitely presented, simple and MIF. A general
  finitely generated `A ∈ B_A` embeds in such an `M` by BFFHZ Theorem C only
  after passing to a finitely presented simple envelope. An automorphism of `A`
  need not extend to that envelope.
- **Ascending only.** For a non-ascending edge `phi = β|_(C_1) : C_1 -> C_2`
  with `C_1, C_2 <= A <= Q`, the subgroup `< A, t >` of `Q ⋊_β Z` is `A *_phi`
  only when the subgroups `β^i(A)` generate their bi-infinite tree product
  inside `Q`. In the free-factor examples this either fails or the HNN extension
  collapses by Tietze moves to a free product. See
  `notes/bh-embeddability-survives-decidable-edge-swarm-2026-09-16.md`.
- **Automorphism-induced edges.** Every edge map reached is the restriction of an
  automorphism `β` of `M * F_m`. Let `A <= M * F_m` be nontrivial, freely
  indecomposable and not infinite cyclic, and let `1 != C_2 = β(C_1) <= A`.
  Then `A` lies in a conjugate `gMg^-1` by Kurosh. `β(gMg^-1)` is again a
  conjugate of `M` and meets `gMg^-1` in `C_2 != 1`, so by malnormality it is
  `gMg^-1`. Hence the edge map is, up to conjugation by `g`, the restriction of
  an automorphism of `M`. Partial isomorphisms that extend to no automorphism of
  any finitely presented simple MIF overgroup are out of reach of this construction.

## Update (bh-free-05, 2026-09-18)

Related: `ascending-hnn-of-free-groups-satisfy-boone-higman` (b6bb206cf, lane proof) covers ascending HNN extensions of finitely generated free groups along arbitrary injective endomorphisms, not only those induced by automorphisms. It uses a different mechanism, BLIW's BS_{F_2} theorem after a Hall extension. The two results overlap only on free bases, since this node needs a finitely presented simple MIF factor M.
