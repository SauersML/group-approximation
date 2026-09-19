---
rg: 2
id: ck-envelope-simple-core-has-finite-bi-index
kind: claim
title: The normal-generator envelope can be chosen so that the simple core has finitely many double cosets
distinct_from:
  finite-infranormal-subgroup-is-normal: that concerns finite subgroups and their normalizers; this concerns finiteness of a DOUBLE COSET SPACE of an infinite, non-normal subgroup, where neither the subgroup nor its index is finite.
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that asks for a compactness property of the normal lattice of the envelope; this asks for a finiteness property of the double coset space of one subgroup pair. Neither implies the other by any argument found in this audit, and they feed different routes into the same target.
  simple-core-bi-index-counts-coset-action-pair-orbits: that PROVES the coset action is faithful and identifies its pair-orbits with double cosets, for any envelope; this asserts that the count can be made finite, which is the open part and is a statement about the construction rather than about the action.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

The embedding of `chatterji-kassabov-normal-generator-embedding` can be
arranged so that, in addition to its stated conclusions, the simple core `S`
satisfies

    | S \ Gamma / S |  <  infinity .

Open.  Nothing in the known construction bears on double cosets at all.

## Why it would finish

By `simple-core-bi-index-counts-coset-action-pair-orbits` the coset action
`Gamma` on `Gamma/S` is then faithful, has finitely generated point
stabilizer `S`, and has finitely many orbits on pairs, while `Gamma` is
finitely presented.  Those are exactly the hypotheses of
`twisted-brin-thompson-finite-presentation-criterion`, so `SV_Gamma` is a
finitely presented simple group, and it contains `Gamma`, hence `S`, hence
the original group.

The appeal of the route is that it never chooses a maximal normal subgroup
and never asks for a finite normal generating set.  It replaces the
normal-lattice question of
`ck-envelope-has-a-finitely-normally-generated-maximal-kernel` with a
double-coset question, which is a different kind of object with different
tools.

## Attempts

1. **Read it off the existing construction.**  *Fails immediately.*  The
   Chatterji--Kassabov proof controls a normal-generation relation and a
   presentation; it says nothing about `S \ Gamma / S`, and the intermediate
   objects — a group ring, a ring extension, an elementary matrix group —
   carry no double-coset bookkeeping to inspect.  With
   `universal-sandwich-ring-is-finitely-presented-and-injective` the envelope
   is now the explicit `EL_4(U)`, so the double cosets of `S` in a matrix
   group over an explicit finitely presented ring are at least a concrete
   object to compute with.  Nothing was computed here.
2. **Derive finiteness from the normal-generation property.**  *No
   implication found.*  Normal generation constrains the normal closure of
   one element; a bi-index bound constrains the whole double coset space.
   The near-solution says every proper normal subgroup misses `S`, which is
   compatible with `S` being, for instance, of infinite index with
   infinitely many double cosets.
3. **Enlarge `S` until the bi-index drops.**  *Deferred, and the obvious
   version is self-defeating.*  Bi-index falls as the subgroup grows, and at
   `S = Gamma` it is 1 — but then the payoff is vacuous, because
   `simple-core-bi-index-counts-coset-action-pair-orbits` degenerates and one
   would already need `Gamma` simple.  A useful version would enlarge `S` to
   some intermediate subgroup that is still simple, or still finitely
   generated with the conjugation property the criterion needs; no such
   intermediate was identified.
4. **Use a different point set than `Gamma/S`.**  *Deferred.*  The criterion
   applies to any faithful action of `Gamma`, not only the coset action on
   `Gamma/S`.  Any faithful `Gamma`-set with finitely many pair-orbits and
   finitely generated point stabilizers would do, and the coset action is
   merely the first candidate because faithfulness is free there by the
   near-solution.  Searching the other faithful actions of `EL_4(U)` is
   untried.
