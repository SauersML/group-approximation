---
rg: 2
id: isolated-vertex-groups-have-fp-stabilizer-engines
kind: claim
title: For every infinite isolated group B (finitely presented and finitely discriminable), the derived full group D(F_B) of Z/2 * B on its compactified Bass–Serre tree is finitely presented
requires:
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
  - free-product-emitter-full-groups-need-isolated-vertex-groups
distinct_from:
  fp-decidable-vertex-groups-have-fp-stabilizer-engines: that assumed only "finitely presented and decidable" and is refuted at B = Z (free-product-emitter-full-groups-need-isolated-vertex-groups); this assumes "isolated", which is necessary.
  free-product-emitter-full-groups-need-isolated-vertex-groups: that proves isolation is necessary; this is the open sufficiency, the "corrected engine conjecture" named in the status of boone-higman-via-fp-stabilizer-engines.
---

**OPEN** (stated by bh-free-56, 2026-09-18; the corrected engine conjecture of the status of
`boone-higman-via-fp-stabilizer-engines`, recorded as a node). Notation as in
`free-product-boundary-groupoids-carry-the-vertex-group-homology`, with `k = 2`.

**Claim (isolated engine conjecture).** If `B` is infinite and isolated, then `D(F_B)` is
finitely presented.

**The hypothesis is necessary.** If `D(F_B)` is finitely presented, then `B` is isolated
(`free-product-emitter-full-groups-need-isolated-vertex-groups`, `stabilizer-engines-are-fp-only-over-isolated-groups`). Isolated groups are finitely presented
and have solvable word problem. So the claim, if true, is a characterization:
`D(F_B)` is finitely presented iff `B` is isolated.

**Why it matters.** With Cornulier–Guyot–Pitsch Question 4
(`every-decidable-group-embeds-in-an-isolated-group`), it implies Boone–Higman
(`boone-higman-via-isolated-stabilizer-engines`).

## First tests

1. **`B` an infinite finitely presented simple group**, such as Thompson's `T` or `V`. Every
   nontrivial normal subgroup is `B`, so no continuity obstruction applies.
2. **`B` finitely presented and virtually simple but not simple**, for example a Burger–Mozes
   lattice whose finite residual is simple of finite index. Finite discrimination holds, but
   `B` is not simple.

## What any proof must do

- **Use finite discrimination at the emitter.** The proof of necessity shows where it enters.
  The missing relations around a vertex are exactly those that fail when `B` is replaced by
  nearby marked groups. So a proof must derive them from relations that "see" the finite
  discriminating set of `B`.
- **Stay on the right side of the obstruction.** For `B = Z` these relations are the
  far-commutation relations of the local `H_2`, and they are underivable.

## Lesson for general BH

The engine question is now correctly posed. The input class is exactly the class that marked
group limits cannot distinguish from nearby quotients, namely the isolated groups. The emitter
then has to convert isolation (finite presentation plus a finite normal-subgroup detector) into
finite presentation of the simple host. That conversion is where any positive proof must live.
