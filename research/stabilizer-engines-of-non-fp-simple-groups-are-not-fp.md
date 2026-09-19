---
rg: 2
id: stabilizer-engines-of-non-fp-simple-groups-are-not-fp
kind: claim
title: The stabilizer engine D(F_S) of a finitely generated simple group S that is not finitely presented is never finitely presented; S = D(F_(Z wr Z)) is an infinite finitely generated simple group with solvable word problem of this kind
distinct_from:
  simple-inputs-have-finitely-presented-stabilizer-engines: that asserted that D(F_S) is finitely presented for EVERY infinite finitely generated decidable simple S; this refutes it, since the engine is finitely presented only when S already is.
---

**ESTABLISHED** (lane proof, bh-emitter-b, 2026-09-18; elementary given the parent nodes and
Baumslag's theorem that `Z ≀ Z` is not finitely presented; one referee PASS, bh-ref-engines 2026-09-18, see Referee section). Notation `F_B`,
`D(F_B)` as in `free-product-boundary-groupoids-carry-the-vertex-group-homology`, with `k = 2`.

## Statement

1. If `S` is a finitely generated infinite simple group and `D(F_S)` is finitely presented,
   then `S` is finitely presented.
2. `S_0 = D(F_(Z≀Z))` is an infinite, finitely generated, simple group with solvable word
   problem that is not finitely presented. So `D(F_(S_0))` is not finitely presented, and
   `simple-inputs-have-finitely-presented-stabilizer-engines` is false.

## Proof

1. This is `fp-stabilizer-engines-need-fp-vertex-groups` with `B = S`.
2. Put `B = Z ≀ Z`.
   - **Simple, infinite, finitely generated.** By the parent node, `D(F_B)` is simple,
     finitely generated because `B` is. It is infinite: for `b ∈ B \ 1` and `a` the generator
     of `Z/2`, the commutator `[b, a] = b a b^{-1} a` is cyclically reduced of length 4 in
     `Z/2 * B`, so it has infinite order, and it lies in `[F_B, F_B]`.
   - **Not finitely presented.** If `D(F_B)` were, then `B` would be, by
     `fp-stabilizer-engines-need-fp-vertex-groups`. But `Z ≀ Z` is not finitely presented
     (G. Baumslag, Math. Z. 75 (1961)).
   - **Solvable word problem.** This is the lemma below, applied to `B = Z ≀ Z`, which has
     solvable word problem.
   - Then apply part 1 to `S_0`. `∎`

**Lemma.** If `B` is finitely generated with solvable word problem, then `F_B` has solvable
word problem. Hence so does every finitely generated subgroup, including `D(F_B)`.

*Proof.*
- **Encoding.** Encode an element of `F_B` as a finite list of pairs (clopen piece,
  label in `D`). The pieces are finite Boolean combinations of half-trees, and a half-tree
  is named by a directed edge, i.e. by an element of `D` and an orientation. Reduced words
  in `D = Z/2 * B` are computable from a solution of the word problem of `B`.
- **Computable operations.**
  - The image of a half-tree under a label is a half-tree, computable from reduced words.
  - The relative position of two directed edges (nested, disjoint or co-disjoint
    half-trees) is read off from the reduced form of `d^{-1} d'`.
  - So products of encoded elements are computable.
- **Nonempty pieces.** Whether a Boolean combination of finitely many half-trees is
  nonempty is decidable. It is a union of components of `T` minus finitely many edges. Such
  a component contains a point of `X` unless it is a single `A`-vertex all of whose `k`
  edges are cut, and that is visible from the finite list of edges.
- **Triviality.** A word is trivial in `F_B` iff every nonempty piece of its computed
  encoding carries the label `1`. This uses local faithfulness of `D` at every point
  (`fp-stabilizer-engines-need-fp-vertex-groups`, step 2). `∎`

## Consequences

- **The route is circular.** `boone-higman-via-stabilizer-engines` is circular as a route: its
  step 3 can hold for an envelope `S` only if `S` is already a finitely presented simple
  group containing the input.
- **The live form of Track C** uses finitely presented, decidable vertex groups that need
  not be simple: `boone-higman-via-fp-stabilizer-engines`.
- **A stock of examples.** For every finitely generated, decidable, non-finitely-presented
  `B`, the group `D(F_B)` is a finitely generated, simple, decidable group that is not
  finitely presented, and it contains every perfect subgroup of its `B`.

## Lesson for general BH

A universal statement "every decidable simple group has a finitely presented engine" cannot
be true for any engine that reads its input through locally faithful labels. Such an engine
retracts onto its input, so it is only as presented as the input. Simplicity of the input
buys nothing on the finiteness side. What must be supplied is a finitely presented,
decidable input, and the engine's job is only to make it simple.

## Referee (bh-ref-engines, 2026-09-18): PASS

- `D(F_{Z≀Z})` is simple (parent) and finitely generated.
- It is infinite: the commutator `[b, a]` has infinite order in `Z/2 * B`.
- It is decidable, by the lemma: nonemptiness of atoms is decidable from the finite edge list.
- It is not finitely presented, by Baumslag (Math. Z. 1961) through the quasi-retraction.
- The refutation of `simple-inputs-have-finitely-presented-stabilizer-engines` stands. It is
  now also implied by `stabilizer-engines-need-torsion-vertex-groups`, since infinite simple
  vertex groups are excluded outright.
