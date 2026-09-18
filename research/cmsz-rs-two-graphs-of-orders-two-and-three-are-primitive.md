---
rg: 2
id: cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive
kind: claim
title: The Robertson–Steger 2-graphs of seven explicit CMSZ groups (five of order 2, two of order 3) are primitive and aperiodic, so these groups embed in finitely presented simple groups modulo the unpinned k-graph standard facts
distinct_from:
  cmsz-pg22-rs-two-graphs-admit-no-brick-coding: that shows the same five order-2 tile 2-graphs have no brick coding, which closes the mV route; this shows they, and two order-3 ones, are primitive and aperiodic, which is what the Li–Matui route needs.
  robertson-steger-a2-two-graphs-are-primitive-and-aperiodic: that is the general claim, which is false for type-preserving groups (rs-strip-tail-transitivity-forces-primitive-transition-matrices); this certifies explicit type-transitive instances.
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-cmsz-primitivity-certificate.md
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (lane computation plus lane proof, bh-groupoid 2026-09-18; not
independently reviewed; no novelty claimed).

## Statement

The inputs are the triangle presentations recorded in the repo:
- `T0`–`T4` over `PG(2,2)`: `experiments/nv-brick-coding-2026-09-17/tp_q2.json`, the five
  point–line bijections listed in `cmsz-pg22-rs-two-graphs-admit-no-brick-coding`;
- two presentations over `PG(2,3)`: `tp_q3.json` in the same directory.

For each such `T`, let `Λ_T` be the tile 2-graph built by `rs2graph.py`, with
`(q²+q+1)(q+1)q` tiles (42 or 156). Then:

1. `M_1` and `M_2` are primitive, with exponents 4 or 5 (per-example values in the log).
   `M_1 + M_2` is primitive with exponent 3.
2. `Λ_T` is aperiodic in the Kumjian–Pask sense.
3. Let `Γ_T = ⟨a_x | a_x a_y a_z = 1, (x,y,z) ∈ T⟩` be the CMSZ group. It embeds in a
   finitely presented simple group, conditional only on
   `finite-k-graph-boundary-groupoid-standard-facts`.

## Proof

**Item 1.** This is an exact computation on MSI, calibrated, with two independent
primitivity tests and two independent constructions of the edge sets. See
`research/artifacts/gq-bh-bh-groupoid-cmsz-primitivity-certificate.md` for the script, the
log and the edge rule matched against Robertson–Steger §7.

**Item 2.**
- (H3) holds for Robertson–Steger 2-graphs of vertex-free groups
  (`robertson-steger-a2-boundary-algebras-are-rank-two-ck`).
- `Λ_T` has no sources, since the row sums are `q²`.
- Apply `rs-two-graph-aperiodicity-from-h3-and-irreducibility`.

**Item 3.** Four inputs.
- **CMSZ action.** `Γ_T` acts simply transitively and type-rotatingly on the vertices of an
  Ã₂ building whose Cayley complex is the building (CMSZ I, Theorem 3.4, as cited in
  `experiments/nv-brick-coding-2026-09-17/tp.py`; not re-read at source).
- **Λ_T is the Robertson–Steger 2-graph of Γ_T.**
  - Because the action is simply transitive, `A = Γ\𝔗` is the set of tiles at the identity
    vertex, that is, label tuples `(x,y,z,u,w)` with `u ≠ z`.
  - The edge rule is RS's `M_1`, `M_2`, as matched in the artifact.
- **Embedding.** `a2-group-embeds-in-full-group-of-its-rs-two-graph` embeds `Γ_T` in
  `[[G_{Λ_T}]]`.
- **Simple host.** `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple` needs
  exactly items 1 and 2, and is open only through the standard-facts node. ∎

## Scope

- Nothing here decides whether these seven buildings are exotic.
  - Bader–Caprace–Lécureux (arXiv:1608.06265, §`sec:ReviewExotic`, read at source) list 65
    exotic CMSZ buildings of order 3, with vertex-regular lattices.
  - For order 2 they list only the Tits–Ronan chamber-regular examples and Barré's example
    as exotic.
  - The two order-3 presentations here were found at random, and are not matched to CMSZ's
    tables.
- If a building is Bruhat–Tits, `Γ_T` is linear, and Boone–Higman for it is already known
  through the linear-group nodes. The new content is for exotic ones, and for the method.
- **What would close all 65 exotic order-3 buildings.** An exhaustive enumeration of the
  triangle presentations over `PG(2,3)`, followed by the same primitivity check. That is
  heavier than the approved budget and was not run.
