---
rg: 2
id: fg-perfect-wreath-c2-has-property-fa
kind: claim
title: For a finitely generated perfect group A the wreath square (A x A) ⋊ C_2 has Serre's property FA
distinct_from:
  property-t-implies-property-fa: that certifies FA through property (T), which a wreath square of an arbitrary perfect group does not have; this certifies FA with no rigidity input, from perfectness and the swap alone, and the factor A itself may split as an amalgam.
  fa-subgroups-of-graph-towers-lie-in-base-pieces: that is the consequence of FA for subgroups of graph towers; this is a source of FA groups containing a prescribed group, which that claim then pins into a base piece.
  permutational-boone-higman-closed-under-wreath-products: that is a permanence of the permutational Boone--Higman class under wreath products; this is a fixed-point property of one wreath product and says nothing about embeddings into simple groups.
artifacts: [research/artifacts/fg-perfect-wreath-c2-fa-citation-2026-09-17.md, research/artifacts/fg-perfect-wreath-c2-fa-proof-2026-09-17.md]
---

**OPEN.** Two routes are drafted as artifacts but not yet fully refereed.

Let `A` be a finitely generated perfect group and `W = A wr C_2 = (A x A) ⋊ C_2`,
where the generator `sigma` of `C_2` swaps the two factors. Then every action of
`W` on a tree (without inversions) has a global fixed point.

This holds although `A` itself need not have FA: for instance a finitely
generated simple group that splits as a nontrivial amalgam.

- The citation artifact imports the general criterion of
  Cornulier--Kar: `A wr B` has FA iff `B` has FA and `A` is finitely generated
  with finite abelianisation. Here `B = C_2` is finite.
- The proof artifact is a self-contained two-paragraph proof for the
  perfect case, which is all that `decidable-groups-have-decidable-fa-envelopes`
  consumes.

## Attempts

1. **Cornulier--Kar import and a self-contained axis argument (2026-09-17).** See `research/artifacts/fg-perfect-wreath-c2-fa-citation-2026-09-17.md` and `research/artifacts/fg-perfect-wreath-c2-fa-proof-2026-09-17.md`. The proof reduces to one factor, takes a hyperbolic element of `A_1`, and shows that `A_2` fixes its axis pointwise, using perfectness against `D_inf`. Lens 2 of the referee panel lost its vote, so the result is recorded as an attempt, not established. Lenses 1 and 3 both returned *survives* and found no mathematical gap. *Pending referee.* Restore both as routes once a full referee pass survives.
