---
rg: 2
id: fp-decidable-vertex-groups-have-fp-stabilizer-engines
kind: claim
title: For every infinite finitely presented group B with solvable word problem, the derived full group D(F_B) of Z/2 * B on its compactified Bass–Serre tree is finitely presented
distinct_from:
  simple-inputs-have-finitely-presented-stabilizer-engines: that asked the same for finitely generated decidable SIMPLE vertex groups and is refuted (stabilizer-engines-of-non-fp-simple-groups-are-not-fp); this asks it for finitely presented decidable vertex groups, which are exactly the vertex groups the known obstructions allow.
  fp-stabilizer-engines-need-fp-vertex-groups: that is the necessity of "B finitely presented"; this is the open sufficiency of "finitely presented and decidable".
  reid-higman-thompson-variant-d-zero-abelianization: that is the case B = Z (Reid's group), which is not finitely presented (free-product-emitter-full-groups-need-isolated-vertex-groups); this is the general statement.
refuted_by:
  - free-product-emitter-full-groups-need-isolated-vertex-groups
  - stabilizer-engines-need-finitely-discriminable-vertex-groups
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `free-product-boundary-groupoids-carry-the-vertex-group-homology`.

**REFUTED (2026-09-18)** by `free-product-emitter-full-groups-need-isolated-vertex-groups`.
- A finitely presented `D(F_B)` forces `B` to be *isolated*: finitely presented and
  finitely discriminable.
- `B = Z` is finitely presented and decidable, but it is residually finite, hence not
  finitely discriminable. So `D(F_Z)` (Reid's group) is not finitely presented.
- The corrected conjecture is still open: every infinite isolated `B` gives a finitely
  presented `D(F_B)`.

The refuted statement is kept below as a record.

Refuted statement (stated by bh-emitter-b, 2026-09-18). Notation as in
`free-product-boundary-groupoids-carry-the-vertex-group-homology`, with `k = 2`.

**Claim (stabilizer engine conjecture).** If `B` is an infinite finitely presented group with
solvable word problem, then `D(F_B)` is finitely presented.

**Both hypotheses are necessary.** If `D(F_B)` is finitely presented, then:
- `B` is finitely presented (`fp-stabilizer-engines-need-fp-vertex-groups`);
- `B` has solvable word problem (`fp-stabilizer-engines-need-decidable-vertex-groups`).

So the claim, if true, is a characterization: `D(F_B)` is finitely presented iff `B` is
finitely presented and decidable.

**Why it matters.** It implies Boone–Higman through `boone-higman-via-fp-stabilizer-engines`.
There it is used only for vertex groups `B = B_0 ≀ Z/2` with `B_0` finitely presented and
decidable.

## What any proof must do

1. **It must consume the word problem.** For a finitely presented `B` with unsolvable word
   problem, all local data are still finite: `B` is finitely presented, and the tree and the
   prefix actions are the same. Yet `D(F_B)` is not finitely presented. So no argument that
   uses only finite presentation of the local groups can work. For example, a Brown-criterion
   proof must have a descending-link connectivity step that fails for undecidable `B`.
2. **It must pass Reid's group.** The first case, `B = Z`, fails: `D(F_Z)` is not finitely presented (see the banner).
3. **It must control the emitter.** Near the emitter `v` the local group contains copies of
   `FSym(B) ⋊ B`, a Houghton-type group (`H_2` for `B = Z`, not finitely presented). The
   missing relations must follow from relations supported away from `v`, through the
   self-similarity `X = {v} ⊔ ⊔_(b ∈ B) bH` with `H ≅ K = X \ H`.

## Lesson for general BH

With the non-finitely-presented vertex groups removed by a quasi-retraction, the stabilizer
engine becomes a clean Boone–Higman-shaped statement. The input is finitely presented and
decidable, the output is finitely presented and simple, and the only mechanism in between is
one infinite emitter. The word problem must enter through the emitter's relations. That makes
(IE) the place where decidability is converted into finite presentation.
