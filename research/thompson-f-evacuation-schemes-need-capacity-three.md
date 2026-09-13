---
rg: 2
id: thompson-f-evacuation-schemes-need-capacity-three
kind: claim
title: Every evacuation scheme on the {x_0, x_1} Cayley graph of Thompson's group F has capacity at least three
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that lower-bounds the size of Følner sets as epsilon tends to zero; this is a bound on the capacity of evacuation schemes, forced by one finite subgraph of density above 3.5.
  thompson-f-is-not-amenable: that is non-amenability, equivalent to the existence of an evacuation scheme of some finite capacity; this rules out only capacities one and two for one generating set.
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md
---

**ESTABLISHED.** An evacuation scheme of capacity `C` on a Cayley graph assigns to each vertex
`v` an infinite simple path `p_v` from `v`, with every directed edge on at most `C` of the
paths. `F` is non-amenable iff such a scheme exists for some `C` (V. Guba, *Amenability
problem for Thompson's group F: state of the art*, arXiv:2305.07113v4, §2, Proposition 2.4).

For the Cayley graph of `F` with respect to `{x_0^(±1), x_1^(±1)}`, no scheme of capacity 1
or 2 exists.

**Mechanism.** In a `2m`-regular graph, a finite vertex set `A` of average induced degree
`δ(A)` has exactly `(2m - δ(A))|A|` outward directed boundary edges. Every path `p_v`,
`v ∈ A`, uses one of them, so capacity `C` forces `δ(A) ≤ 2m - 1/C`. Guba
(arXiv:2210.12304; survey Theorem 2.8) gives finite subgraphs of density `> 3.5 = 4 - 1/2`
for `{x_0, x_1}`.

**Scope.** This decides nothing: capacity 3 and above stays open, and the problem is equivalent
to the existence of some finite capacity. It corrects the line "open for `C >= 2`" in
`research/artifacts/thompson-f-certificate-shapes-2026-09-12.md` for the generating set
`{x_0, x_1}`. The survey's density theorem was read from an ar5iv render by a summarizing
fetch on 2026-09-13, and the density number already appears on main in
`thompson-f-is-amenable`.

Proof route: `thompson-f-evacuation-schemes-need-capacity-three-proof`.
