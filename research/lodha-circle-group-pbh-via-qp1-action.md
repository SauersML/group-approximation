---
rg: 2
id: lodha-circle-group-pbh-via-qp1-action
kind: route
title: Lodha's S is of type (A) on QP^1 by the 2-transitive reduction, so Zaremsky's Corollary B and BFFHZ Theorem C apply
target: lodha-circle-group-satisfies-pbh
requires:
  - lodha-circle-group-is-finitely-presented-and-simple
  - lodha-circle-group-infinity-stabilizer-is-fg
  - two-transitive-action-reduces-type-a-to-two-clauses
  - type-a-action-gives-boone-higman-for-subgroups
  - fp-simple-highly-transitive-groups-satisfy-pbh
artifacts:
  - research/artifacts/lodha-circle-group-type-a-action-2026-09-16.md
---

This is §9 of `research/artifacts/lodha-circle-group-type-a-action-2026-09-16.md`.

**Part 1: type (A).**
- By `lodha-circle-group-infinity-stabilizer-is-fg` part 1, `S` preserves `QP^1` and acts on
  it faithfully and 2-transitively. Also `|QP^1| ≥ 2`.
- By `lodha-circle-group-is-finitely-presented-and-simple` part 1, `S` is finitely presented.
- By `lodha-circle-group-infinity-stabilizer-is-fg` part 2, the point stabilizer `Stab_S(∞)`
  is finitely generated.
- `two-transitive-action-reduces-type-a-to-two-clauses` turns these facts into: the action
  of `S` on `QP^1` is of type (A).

**Part 2: subgroups.** Let `H ≤ S`. Then `H` embeds in a group with a type (A) action, namely
`S` itself. This is the definition of permutational Boone--Higman used in BFFHZ Theorem C (i),
as quoted in `fp-simple-highly-transitive-groups-satisfy-pbh`: "it embeds in a group admitting
an action of type (A)". Zaremsky's Corollary B, imported as
`type-a-action-gives-boone-higman-for-subgroups`, gives solvable word problem for `H` and an
embedding of `H` in a finitely presented simple group.

**Part 3: MIF and highly transitive overgroups.**
- `S` is finitely generated, by part 2 of `lodha-circle-group-is-finitely-presented-and-simple`:
  `S = ⟨a, b, l, s⟩`.
- `S` has solvable word problem, by Part 2 applied to `H = S`.
- So BFFHZ Theorem C, imported as `fp-simple-highly-transitive-groups-satisfy-pbh`, applies
  to `G = S`. Its hypothesis reads: "For a finitely generated group G (with solvable word
  problem)".
- (i) holds by Part 1. Then (i) ⟹ (iv) gives an embedding of `S` in a finitely presented
  simple MIF group, and (i) ⟹ (iii) an embedding in a finitely presented simple highly
  transitive group. ∎

No Lean counterpart.
