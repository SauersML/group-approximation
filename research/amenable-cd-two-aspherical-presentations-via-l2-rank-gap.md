---
rg: 2
id: amenable-cd-two-aspherical-presentations-via-l2-rank-gap
kind: route
title: An L2-rank gap makes a finitely generated amenable cd-2 group BS(1,m), whose one-relator presentation is aspherical with free second syzygy
target: amenable-cd-two-groups-have-aspherical-presentations
requires:
  - amenable-cd-two-groups-have-an-l2-rank-gap
  - amenable-cd-two-l2-rank-gap-forces-baumslag-solitar
---

Let `G` be finitely generated and amenable with `cd G = 2`. By
`amenable-cd-two-groups-have-an-l2-rank-gap`, `Z[G]` has an `L²`-rank gap. Item 3 of
`amenable-cd-two-l2-rank-gap-forces-baumslag-solitar` then gives `G ≅ BS(1,m) = ⟨a, t | t a t⁻¹ a⁻ᵐ⟩`
with `m ≠ 0`.

The relator is not a proper power in the free group on `a, t`. Lyndon's identity theorem
(recalled) makes the presentation complex `X` aspherical. Its cellular chain complex over
`Z[G]` is the free resolution `0 → Z[G] → Z[G]² → Z[G] → Z → 0`, and the middle map sends
`e_a ↦ a − 1` and `e_t ↦ t − 1`. So with generating set `x_1 = a`, `x_2 = t`, the second syzygy
`P = ker(Z[G]² → Z[G])` is the image of `Z[G] → Z[G]²`. That map is injective, so `P ≅ Z[G]` is
free. This gives both forms of the target, with `d = 2` and `|R| = 1 = d − 1`. ∎

The converse holds, but it is not recorded here, which keeps the graph acyclic. The target implies
Kropholler's question in dimension 2 by item 3(c) of `amenable-free-top-syzygy-forces-type-fp`.
That implies the gap, with value 1, by item 4 of
`amenable-cd-two-l2-rank-gap-forces-baumslag-solitar`. So the gap claim is an equivalent form of
the target. It asks only for a lower bound on the `L²`-ranks of single elements. It does not ask
for freeness of `P`.
