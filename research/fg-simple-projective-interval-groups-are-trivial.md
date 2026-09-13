---
rg: 2
id: fg-simple-projective-interval-groups-are-trivial
kind: claim
title: Every finitely generated simple group of piecewise-projective homeomorphisms of a compact interval is trivial
distinct_from:
  thompson-f-has-no-free-subgroups: that is the Brin--Squier theorem that F has no non-abelian free subgroups; this is a germ argument showing F, PL_+[0,1] and their piecewise-projective relatives have no nontrivial finitely generated simple subgroups
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part1.md
---

**ESTABLISHED.**

**Setting.** `PP_+(I)` is the group of orientation-preserving homeomorphisms of a
compact interval `I` that are piecewise real projective with finitely many pieces.
It contains `PL_+(I)`, and hence Thompson's group `F` on `[0, 1]`.

**Statement.**
1. Let `G ≤ PP_+(I)` be nontrivial and finitely generated. Then `G` fixes
   `c = inf` of the union of the supports of its generators, and the germ at `c`
   from the right is a homomorphism from `G` onto a nontrivial subgroup of the
   metabelian group of projective maps fixing `c`.
2. So every finitely generated simple subgroup of `PP_+(I)` is trivial.

**Consequences.**
- No infinite simple group answering Zaremsky Problem 1.10 lies in `F`,
  `PL_+[0,1]` or `PP_+(I)`. Amenability of `F` would not supply a candidate inside `F`.
- Model tests: `F'` is simple but not finitely generated; Thompson's `T` is finitely
  generated and simple but acts on the circle, with no fixed endpoint.

**Proof:** `fg-simple-projective-interval-groups-are-trivial-proof`.
