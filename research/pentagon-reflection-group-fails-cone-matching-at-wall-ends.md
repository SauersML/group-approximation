---
rg: 2
id: pentagon-reflection-group-fails-cone-matching-at-wall-ends
kind: claim
title: The right-angled pentagon reflection group fails cone matching along four persistent chains of atoms per generator (the wall-endpoint branch points), so condition (C) is not the route even for cubulated hyperbolic groups; colour-tameness of a tile operad means every colour has an operation with inputs of that colour only, which fails already for free groups and holds after Cuntz stabilization
requires:
  - hyperbolic-cone-matching-holds-off-the-branch-locus
artifacts:
  - research/artifacts/gq-bh-finf-hyp-cone-matching-test.md
distinct_from:
  hyperbolic-cone-matching-holds-off-the-branch-locus: that proves cone matching off the branch locus and reduces square filling to the automaton condition (C); this tests (C) on a hyperbolic group, finds it failing at branch points, and settles the colour-tameness gate.
---

**Status.**
- **Item 1 is computational evidence.** Each reported failure is certified exactly at its level,
  and the mechanism is proposed, not proved. No priority is claimed.
- **Item 2 is ESTABLISHED** (lane proof, not reviewed).

## 1. Cone matching fails on a hyperbolic reflection group

One Slurm job (1328148, 19 s) ran the test in the artifact on right-angled Coxeter groups with
their standard generators. Word lengths there are exact.

- **Calibration.** On the tree `Z/2*Z/2*Z/2`, the only failure is at level 1, as predicted.
- **Positive control.** The grid `D_∞ × D_∞` fails at its 4 corners at every level from 1 to 9.
- **The right-angled pentagon group.** This group is hyperbolic, with boundary `S^1`. For every
  generator and every level `n = 1, …, 5`:
  - exactly 4 atoms `D` have `kD` provably not an atom;
  - they form nested chains through all computed levels.

  The signature is the same as the grid's.
- **Proposed mechanism.** A generator is the reflection in a wall.
  - At the two wall endpoints, the fibre of `∂_h G → ∂G` has one horofunction for each side of
    the wall.
  - A front window there straddles the wall, and `d(k, ·) − d(1, ·) = ±1` on the two sides.
  - So the balls `kB_n` and `B_m` never agree on the front. This is exactly the branch-point case
    that Theorem 1 of the parent excludes.
- **Consequence.** The persistent chains mean the reflection's local actions along the wall
  endpoints stay non-surjective. So the nucleus automaton has an infinite non-surjective path,
  hence a cycle in `N'`, and (C) fails, assuming the pattern persists beyond level 5 as it does
  for the grid.
- **The route is wrong, not the group.** The pentagon group is cubulated, and it already has
  F_∞ simple hosts through `2V`. So the nucleus-tile operad with cone and tile insertions is the
  wrong operad, already for easy hyperbolic groups.

## 2. Colour-tameness: a criterion, and how to obtain it

**Proposition.** Let `𝒪` be a symmetric operad with transformations and finitely many colours.
Then `𝒪` is colour-tame (Thumann, Def. `77101`) if and only if every colour `c` is the output of
some operation of degree at least 2 whose inputs all have colour `c`.

**Proof.**
- **Direction of arrows.** In Thumann's `𝒮(𝒪)`, an arrow has as domain the concatenated
  *input* colours (TeX l.1783–1789). So `X` is reduced when no sub-multiset of `X` is the input
  multiset of a higher-degree operation.
- **If.** If colour `c` has such an operation with `k_c` inputs, then a reduced object has fewer
  than `k_c` entries of colour `c`. Its degree is therefore at most `Σ_c (k_c − 1)`.
- **Only if.** If colour `c` has no such operation, then `(c, …, c)` is reduced at every length. `∎`

**Consequences.**
- **Failure without stabilization.** Let `𝒪` be the canonical operad of a subshift of finite type,
  or the nucleus-tile operad `𝒪_Nuc`, and suppose some cycle of the core avoids a node `v`.
  - A cone can then never be partitioned into cones of type `v`, since an infinite path avoids `v`.
  - Transformations cannot recolour cones, because morphisms preserve type.
  - So colour-tameness **fails**. This already happens for the free group on a basis, whose
    letters `b b b ⋯` avoid the type `a`.
- **Cuntz stabilization repairs it.** Replace every colour `c` by `c × {x,y}^ℕ`, and add the split
  `c × {x,y}^ℕ = (c × x{x,y}^ℕ) ⊔ (c × y{x,y}^ℕ)`. Both inputs have colour `c`, so the stabilized
  operad is colour-tame.
  - Stabilization leaves the host containing `H`, acting on the first coordinate.
  - It does not change cone matching, which lives on the first factor.

  This is the same mechanism that makes Cuntz-stabilized Li–Garside full groups F_∞
  (`cuntz-stabilized-garside-full-groups-are-f-infinity`): every piece can merge with a copy of
  itself.

## Lesson for general BH

- **Test the finiteness engine first, on groups whose answer is known.** Run the test on the
  tree, the grid and a reflection group. The pentagon group's host is known to be F_∞, yet the
  engine fails there, at the branch points. So the nucleus-tile operad cannot certify F_∞, even
  for cubulated groups.
- **What the failures look like, and the repair they suggest.** They sit at corners:
  horofunctions from the two sides of a wall. A repair must merge each such pair into one tile,
  which gives a configuration insertion over the finitely many configuration types of
  `horofunction-atom-configurations-have-finitely-many-types`.
- **Colour-tameness is never the obstacle.** It is exactly "every colour splits into copies of
  itself". Cuntz stabilization gives that for free.

## Next

- **The one open gate.** Test configuration matching. Does each generator map the union of the
  paired atoms at a wall endpoint (both sides) onto the union of the image pair? This needs one
  more job, with the same code plus unions of the 4 bad atoms.
- **What each outcome means.**
  - If configuration matching holds, add configuration tiles to `𝒪_Nuc`. Square filling then
    reduces to the configuration version of (C), which is a finite check.
  - If it fails, the corner behaviour is intrinsic, and a Thumann operad on atom shadows cannot
    give F_∞. The F_∞ half for Kazhdan inputs would then need a different complex.
