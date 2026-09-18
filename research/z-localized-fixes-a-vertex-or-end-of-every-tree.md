---
rg: 2
id: z-localized-fixes-a-vertex-or-end-of-every-tree
kind: claim
title: Every action of Z_(l) on a simplicial tree fixes a vertex or an end, so in a graph of groups Z_(l) lies in a vertex group or in an ascending union of edge groups along a ray
distinct_from:
  fg-metabelian-groups-have-roots-at-finitely-many-primes: that excludes finitely generated metabelian hosts algebraically; this constrains hosts that split as graphs of groups, through their Bass-Serre trees.
  free-group-mapping-tori-contain-no-z-localized: that applies the present lemma to ascending HNN extensions of free groups.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**ESTABLISHED (2026-09-18)** through `z-localized-fixes-a-vertex-or-end-of-every-tree-proof`. Lane proof (gq-k2-q),
elementary, not independently reviewed. No novelty is claimed.

## Statement

Let `A ≤ (Q, +)` contain an element `a ≠ 0` that is divisible in `A` by infinitely many primes. This includes
`Z_(l)`, `Z[1/P]` for any infinite set `P` of primes, and `Q`.
Let `A` act on a simplicial tree `T` without inversions.

1. Every element of `A` is elliptic.
2. `A` fixes a vertex of `T`, or fixes an end `ω` of `T`. In the second case, for any ray `(v_k)` towards `ω`, the
   groups `A ∩ Stab(v_k)` increase eventually and have union `A`.
3. **Graphs of groups.** If a group `Λ` is the fundamental group of a graph of groups and contains `A`, then either
   `A` is conjugate into a vertex group, or `A` is the increasing union of its intersections with the stabilizers
   of the vertices of a ray. Each such intersection lies in a conjugate of a vertex group, and consecutive ones lie
   in a common edge stabilizer.

## Consequence for the Z_(l) bottleneck

A finitely presented residually finite witness `Λ` for `z-localized-embeds-in-fp-rf-group` that splits over its
Bass–Serre tree must realize `Z_(l)` in one of two ways:
- inside a vertex group, which just moves the problem;
- along an ascending chain of vertex stabilizers, as `Z[1/m]` sits along the tree of `BS(1,m)`. This needs roots of
  unboundedly many prime orders to appear in successive vertex groups.
