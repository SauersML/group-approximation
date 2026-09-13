---
rg: 2
id: baumslag-gersten-group-satisfies-boone-higman
kind: claim
title: The Baumslag--Gersten group embeds in a finitely presented simple group
distinct_from:
  one-relator-groups-satisfy-boone-higman: that is Boone--Higman for the whole class of one-relator groups; this is its smallest named torsion-free test case, the Baumslag--Gersten group.
  baumslag-gersten-base-is-elliptic-in-every-tree-action: that is an obstruction to one family of hosts for this group; this is the open embedding question itself.
artifacts:
  - research/artifacts/bh-baumslag-gersten-2026-09-12.md
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

**OPEN.** Let `BG = < a, t | b a b^-1 = a^2 >`, where `b = t a t^-1`. `BG` has
solvable word problem. It is not residually finite, contains `BS(1,2)`, and is
not hyperbolic. By the Boone--Higman theorem it embeds in a simple subgroup of a
finitely presented group. The question is whether some finitely presented simple
group contains it.

## Attempts

- **Tree hosts (dead).** In every action of `BG` on a tree, its `BS(1,2)` base
  fixes a vertex (`baumslag-gersten-base-is-elliptic-in-every-tree-action`). So
  no Bux--Llosa Isenrich--Wu host over virtually free, abelian or nilpotent
  vertex groups contains `BG`.
- **Linear and rooted-tree hosts (dead).** Every finite image of `BG` kills `a`.
  So `BG` is linear over no field and embeds in no self-similar group
  (`baumslag-gersten-group-is-neither-linear-nor-self-similar`). Neither the
  linear-group Boone--Higman classes nor finitely presented self-similar hosts
  can reach it.
- **Odometer and affine models (dead).** An equicontinuous minimal piece for
  `a`, invariant under `b`, forces fixed points, so the affine self-similar
  models of `BS(1,2)` on `Z_p` do not extend (`baumslag-gersten-odometer-pieces-force-fixed-points`).
  The projective 2-adic similarity model fails by counting fixed points. So `a`
  can never act as a fixed-point-free adding machine on the whole space, and an
  odometer piece for `a` that `b` preserves forces a fixed point of `a`
  elsewhere.
- **Röver--Nekrashevych and eventually-similar hosts (open).** `BG` surjects onto
  `Z`, so it has neither FW nor (T).
  `fw-subgroups-of-eventually-similar-groups-virtually-embed` and
  `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` therefore do not
  apply. Those hosts contain non-residually-finite groups such as `V`, so they
  are not excluded. No embedding of `BG` into such a host was found.
- **Rational similarity groups (open).** BBMZ embed every hyperbolic group in a
  full, contracting RSG, through its action on the horofunction boundary.
  `BG` contains `BS(1,2)`, so it is not hyperbolic, and no compact model for it
  is known.
- **Type (A) and twisted Brin--Thompson hosts (open).** By Zaremsky's Theorem A
  (arXiv:2405.18354), `SV_G` is finitely presented exactly when `G` is finitely
  presented and acts faithfully on `S`, with finitely generated point
  stabilizers and finitely many orbits of two-element subsets. Every subgroup
  of such a `G` satisfies Boone--Higman. `BG` acts on the vertices of the
  Bass--Serre tree of its HNN structure with stabilizers conjugate to
  `BS(1,2)`. But tree distance is unbounded, so there are infinitely many
  orbits of two-element subsets. No type (A) action of `BG`, or of a finitely
  presented overgroup, was found.

See `research/artifacts/bh-baumslag-gersten-2026-09-12.md` for the host table.
