---
rg: 2
id: z3-free-z-does-not-embed-in-2v
kind: claim
title: The right-angled Artin group Z^3 * Z does not embed in the Brin-Thompson group 2V
distinct_from:
  z3-free-z-embeds-in-gl8z: that embeds Z^3 * Z in GL_8(Z); this excludes Z^3 * Z from 2V, and the two together exclude GL_8(Z) from 2V.
refuted_by:
  - z3-free-z-embeds-in-brin-thompson-group-2v
---

`Z^3 * Z` is not isomorphic to any subgroup of `2V`.

**Source.** This is the case `n = 2`, `Γ` = triangle plus an isolated vertex, of
Belk–Bleak–Matucci, arXiv:1602.08635v1, Conjecture 1.7, verbatim: "A
right-angled Artin group A_Γ embeds into nV if and only if A_Γ does not contain
Z^(n+1) * Z."
- The `n = 1` case, "Z^2 * Z does not embed into V", is due to Bleak and
  Salazar-Díaz, as quoted on p. 3 of that paper.
- Their Theorem 1.1 embeds `Z^3 * Z` in `nV` with `n = |V| + |E^c| = 7`.

**What it gives.** With `z3-free-z-embeds-in-gl8z` it answers Zaremsky 2.19(d) no
(`some-gl-n-z-not-in-2v-via-z3-free-z`, witness `GL_8(Z)`). Conversely, a yes to
2.19(d) would put `Z^3 * Z` in `2V` and refute Conjecture 1.7 for `n = 2`.

## Attempts

- 2026-09-13 (lane z2-19-glnz-q-2v, unreviewed): **a germ dimension count
  explains the n + 1.**
  - At a point of `C^n` whose coordinates are all eventually periodic, the germs
    of elements of `nV` fixing the point form `Z^n` (prefix-length shifts in each
    coordinate).
  - If three commuting elements of `2V` fix such a point, the germ homomorphism
    `Z^3 → Z^2` has nontrivial kernel. Some nontrivial element of the `Z^3` then
    acts as the identity near that point.
  - For `n = 1` this is the kind of degeneracy a free letter can be played
    against. The argument of Bleak–Salazar-Díaz was not re-read, so the actual
    proof pattern is unconfirmed.
- 2026-09-13, same lane: **obstacle.** Elements of `2V` can be much wilder than
  elements of `V`.
  - `2V` contains `Q` (`rationals-embed-in-brin-thompson-group-2v`) and
    polylogarithmically distorted elements coming from the SMART reversible
    Turing machine (`brin-thompson-mv-contains-a-distortion-element`). The SMART
    machine has no periodic configurations.
  - So a commuting triple need not have any common periodic point where the germ
    count applies.
  - A proof must either find such points, or replace germs by the offset cocycle
    and invariant measures
    (`heisenberg-in-nv-forces-drift-free-central-element`). The drift map
    `Z^3 → R^2` against a common invariant measure also has nontrivial kernel,
    but a kernel element with zero mean drift can still be nontrivial on every
    open set.
- 2026-09-16 (lane swarm-zaremsky-2-19-embeddings-into-, unreviewed):
  **refuted; the claim is false.**
  - V. Salo, *Graph and wreath products in topological full groups of full
    shifts*, arXiv:2103.06663v1 (11 Mar 2021), proves that every right-angled
    Artin group embeds in the topological full group of a full shift, and that
    this group embeds in `2V`. The abstract says this refutes the Belk–Bleak–
    Matucci conjecture. The preprint predates this node, but the graph had not
    recorded it.
  - Refuter: `z3-free-z-embeds-in-brin-thompson-group-2v`, the graph
    `K_3 ⊔ K_1`, through `every-raag-embeds-in-brin-thompson-group-2v`. Both
    embeddings are reproved from scratch in
    `research/artifacts/raags-in-2v-via-full-shift-full-group-2026-09-16.md`
    (Parts A and B). The belt construction there is a simplified one, checked
    exactly on this graph by
    `experiments/raag-conveyor-belts-full-shift-2026-09-16/belts.py`.
  - Where the 2026-09-13 germ count dies: in the belt embedding, the three
    commuting generators have pairwise disjoint sets of moved points, because
    no position is a cell of belts of two adjacent types. Elements of the `Z^3`
    that act as the identity near a point are then the normal situation, not a
    degeneracy. The kernel of `Z^3 → Z^2` gives no leverage against the free
    letter.
  - Consequence: `some-gl-n-z-not-in-2v-via-z3-free-z` is invalidated. Every
    negative answer to Zaremsky 2.19(d) through a subgroup of `GL_N(Z)` that
    virtually embeds in a finitely generated right-angled Artin group is dead
    (`virtually-special-groups-embed-in-brin-thompson-group-2v`).
