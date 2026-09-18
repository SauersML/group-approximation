---
rg: 2
id: v-and-a-homeomorphism-never-generate-a-free-product
kind: claim
title: A locally moving group and any nontrivial homeomorphism never generate their free product; in particular ⟨V, t⟩ is never V * ⟨t⟩ in Homeo(Cantor)
distinct_from:
  fp-dense-cantor-subgroups-need-not-have-fg-clopen-stabilizers: that claimed ⟨V,t⟩ ≅ V * Z for a comeager set of t; this refutes it by an explicit relation that holds for every t ≠ 1.
  fp-groups-with-a-locally-moving-simple-subgroup-are-isolated: that proves every nontrivial subgroup normalized by a locally moving simple T contains T, via the same double-commutator trick; this isolates the explicit relation and draws the free-product consequence.
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No novelty claimed: this is the
standard double-commutator computation behind the fact that groups with a locally
moving action satisfy mixed identities (they are not MIF).

## Statement

Let `X` be a Hausdorff space, and let `T ≤ Homeo(X)` be a group such that for every nonempty open `U ⊆ X` the
rigid stabilizer `T_U = {g ∈ T : g fixes X − U pointwise}` is nonabelian. Let
`t ∈ Homeo(X)`, `t ≠ 1`.

1. There are a nonempty open `U` with `t(U) ∩ U = ∅` and `a, b ∈ T_U` with
   `[a,b] ≠ 1`. For every such choice,

       [[t,a], b] = [a^{-1}, b]   in Homeo(X),   where [g,h] = g h g^{-1} h^{-1}.

2. The word `w(x) = [[x,a],b] · [a^{-1},b]^{-1}` is a nontrivial element of the free
   product `T * ⟨x⟩` for any cyclic group `⟨x⟩` of order at least 2 (finite or
   infinite). Hence the natural map `T * ⟨t⟩ → ⟨T, t⟩ ≤ Homeo(X)` is never
   injective.
3. In particular, for Thompson's `V` in its standard action on the Cantor set `C`,
   no homeomorphism `t ≠ 1` of `C` satisfies `⟨V, t⟩ = V * ⟨t⟩`. The same holds for
   every group containing `V` in its standard action (for example `nV`, Röver–
   Nekrashevych groups), and for Thompson's `F'` and `T` on the interval and the
   circle.

Item 1 needs `T_U` nonabelian only for the particular small `U` chosen; for `V` on
`C`, `T_U` contains a copy of `V` for every nonempty open `U`.

## Proof

**Choice of `U`.** Since `t ≠ 1`, some `p` has `t(p) ≠ p`. By Hausdorffness pick
disjoint open `A ∋ p`, `B ∋ t(p)`, and let `U = A ∩ t^{-1}(B)`, an open neighbourhood
of `p` with `t(U) ⊆ B`, so `t(U) ∩ U = ∅`. By hypothesis `T_U` is nonabelian; pick
`a, b ∈ T_U` with `[a,b] ≠ 1`.

**The relation.** `a` and `b` are supported in `U` and preserve `U`. The element
`t a t^{-1}` is supported in `t(U)`, which is disjoint from `U`, so `t a t^{-1}`
commutes with every homeomorphism supported in `U`, in particular with `a^{-1}`, with
`b`, and with `a^{-1} b a`. Put `y = a^{-1}` and `z = t a t^{-1}`, so `[t,a] = z y`
with `z` commuting with `y` and with `b`. Then

    [[t,a], b] = z y b y^{-1} z^{-1} b^{-1} = z (y b y^{-1}) z^{-1} b^{-1}
               = (y b y^{-1}) b^{-1} = [y, b] = [a^{-1}, b],

using that `z` commutes with `y b y^{-1}` (supported in `U`). This is item 1.

**Nontriviality in the free product.** Expanding and cancelling the adjacent
`b^{-1} b`,

    w(x) = x · a · x^{-1} · (a^{-1} b a) · x · a^{-1} · x^{-1} · (a^{-1} b^{-1} a).

The syllables alternate between `⟨x⟩` and `T`. Each `⟨x⟩`-syllable is `x^{±1} ≠ 1`
because `⟨x⟩` has order at least 2. Each `T`-syllable is nontrivial: `a ≠ 1` and
`a^{-1} ≠ 1` because `[a,b] ≠ 1`, and `a^{-1} b^{± 1} a ≠ 1` because `b ≠ 1`. By the
normal form theorem for free products, a reduced alternating word of length 8 with
nontrivial syllables is not the identity. So `w(x) ≠ 1` in `T * ⟨x⟩`, while
`w(t) = 1` in `Homeo(X)` by item 1. This is item 2.

**Item 3.** For `V` on `C`, a nonempty open `U` contains a cone `[u]`, and the elements
of `V` supported in `[u]` form a copy of `V`, which is nonabelian. For `F'` on `[0,1]`
and `T` on the circle, every nonempty open set contains an interval supporting a copy
of `F`. ∎

## Consequences

- `fp-dense-cantor-subgroups-need-not-have-fg-clopen-stabilizers` is false as stated:
  its Theorem part 1 asserts `⟨V,t⟩ = V * ⟨t⟩` for a comeager set of `t`, and item 3
  shows this fails for every `t ≠ 1`. Its Baire argument breaks at the claim that
  "freshness makes every point produced by a `v_i` new": the syllables `v_i ∈ V` have
  fixed points with nonempty interior, so a freshly chosen point can be fixed by the
  next syllable and the reading collapses (exactly what happens for `w` above, where
  `a` and `b` fix `t(U)` pointwise). Its part 2 (clopen stabilizers of `V * Z`) is
  about a group that is never realized in `Homeo(C)` this way.
- Consistently with `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`:
  in `⟨V, t⟩` every nontrivial normal subgroup contains `V`, whereas in `V * Z` the
  normal closure of the `Z` factor meets `V` trivially.
- Whether finite presentation plus density in `Homeo(C)` forces finitely generated
  clopen stabilizers is therefore open again (see the updated remark in
  `permutational-boone-higman-iff-dense-cantor-actors`); the claimed witness is gone.
