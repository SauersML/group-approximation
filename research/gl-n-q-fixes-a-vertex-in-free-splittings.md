---
rg: 2
id: gl-n-q-fixes-a-vertex-in-free-splittings
kind: claim
title: GL_n(Q), SL_n(Q), Aff(Q), U_3(Q) and (Q,+) fix a vertex in every action on a tree with trivial edge stabilizers
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem for GL_n(Q); this is a fixed-point property of GL_n(Q) and three of its stepping stones, used to show which host constructions cannot create them.
  bffhz-closures-cannot-create-gl-n-q: that applies this fixed-point property to the free-product and mapping-torus closures around BFFHZ Theorem E; this is the fixed-point property itself.
---

**ESTABLISHED** through `gl-n-q-fixes-a-vertex-in-free-splittings-proof`.
Lane-proved. Independent re-derivation by referee C: PASS
(`research/artifacts/gq-referee-c-bffhz-closures-cannot-create-gl-n-q.md`). The
argument is elementary Bass--Serre theory; no priority is claimed.

## Statement

Let `H` be one of
- `GL_n(Q)` or `SL_n(Q)` with `n >= 2`,
- `Aff(Q) = Q ⋊ Q^x`,
- the Heisenberg group `U_3(Q)` of upper unitriangular `3 x 3` rational matrices,
- `(Q,+)`.

Suppose `H` acts on a simplicial tree `T` without inversions and every edge
stabilizer of the action is trivial. Then `H` fixes a vertex of `T`.

## Consequences

1. **Free products.** If `H` embeds in a free product `A * B`, its image is
   conjugate into `A` or into `B`. Use the Bass--Serre tree of `A * B`.
2. **Graphs of groups with trivial edge groups.** If `H` embeds in the
   fundamental group of such a graph of groups, for instance in `M * F_m`, its
   image lies in a conjugate of a vertex group, for instance of `M`.
3. So no construction that only takes free products, or adjoins free factors,
   can create any of these groups. Divisibility must already be present in a
   vertex group.

## Scope

The statement needs trivial edge stabilizers. With nontrivial edge groups it
fails: `Z[1/2] <= BS(1,2)` fixes only an end of the Bass--Serre tree of the
ascending HNN extension of `Z`. So HNN extensions and amalgams over nontrivial
edge groups are not covered, and they can create divisibility.
