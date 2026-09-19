---
rg: 2
id: reflection-group-atoms-are-roller-cylinders-and-need-walls
kind: claim
title: In a right-angled Coxeter group, horofunction atoms are cylinders of the Roller boundary over the walls meeting the ball, so every non-matching atom maps exactly onto a union of 2^w atoms, where w counts walls through the branch point; the configuration-tile repair of cone matching is the cubical (wall) engine, and for Kazhdan hyperbolic groups it needs a finite-type invariant family of shadow translates that walls cannot supply
artifacts:
  - research/artifacts/gq-bh-finf-hyp-configuration-test.md
distinct_from:
  pentagon-reflection-group-fails-cone-matching-at-wall-ends: that finds the cone-matching failures; this explains them exactly through walls, tests the configuration repair, and shows the repaired engine is the cubical one.
  cuntz-stabilized-garside-full-groups-are-f-infinity: that proves the cubical engine F_infinity after Cuntz stabilization; this shows the horofunction-atom engine for a cubulated group, once repaired, becomes that engine.
---

**Status.**
- **ESTABLISHED (lane proof, not reviewed):** item 1.
- **Computational evidence:** item 2, from one Slurm job (1328791, 37 s). Each failure is exact
  at its level.
- **Reduction:** item 3. No priority is claimed.

## 1. Atoms of a right-angled Coxeter group are Roller cylinders

Let `W` be a right-angled Coxeter group with its standard generators. Its Cayley graph is the
1-skeleton of the Davis complex, a CAT(0) cube complex. Let `𝒲_n` be the set of walls
(hyperplanes) that cross an edge of `B_n`.

**Proposition.**
- For every `x`, the class of `d_x|_{B_n}` modulo constants is determined by the side of `x` of
  each wall in `𝒲_n`, and it determines those sides. So atoms of `B_n` are cylinders of the Roller
  boundary over `𝒲_n`.
- For `g ∈ W`, `gD` is the cylinder over `g𝒲_n`, the walls crossing `gB_n`.
- `gD` is an atom exactly when no wall of `𝒲_m Δ g𝒲_n` (for the relevant `m`) crosses the
  cylinder. Otherwise `gD` is a union of `2^w` cylinders over `𝒲_m ∪ g𝒲_n`, where `w` is the number
  of crossing walls.

**Proof.**
- `d(x, z)` is the number of walls separating `x` from `z`.
- For `z ∈ B_n`, walls not separating `1` from `z` cancel in `d(x,z) − d(x,1)`, so
  `d(x,z) − d(x,1) = Σ_{V ∈ 𝒲(1,z)} ε_V(x)`. Here `ε_V(x) = +1` when `x` is on the side of `1`,
  and `−1` otherwise.
- Conversely, each `V ∈ 𝒲_n` is crossed by an edge `z → z'` of `B_n` with
  `𝒲(1, z') = 𝒲(1, z) ∪ {V}`. Then `ε_V(x) = key(z') − key(z)`.
- The statements about `gD` follow by translating. `∎`

**Why this matches the earlier findings.**
- Near a boundary point `e`, a wall crosses every small cylinder around `e` exactly when `e` is one
  of its endpoints.
- So cone matching (Theorem 1 of `hyperbolic-cone-matching-holds-off-the-branch-locus`) fails
  exactly at wall endpoints, which is the finding of
  `pentagon-reflection-group-fails-cone-matching-at-wall-ends`.
- The image of a bad atom is predicted to be a union of `2^w` atoms, with `w` the number of walls
  of `g𝒲_n Δ 𝒲_m` ending at the point.

## 2. Test of the configuration repair

The test is in the artifact. It computes, for every bad atom, the smallest union `U` of atoms for
which `kU` is exactly a union of atoms.

| group | bad atoms per level | configuration of each bad atom |
|---|---|---|
| tree `Z/2*Z/2*Z/2` | 1 at level 1, then 0 | `U1 -> C2` (the root direction) |
| grid `D_∞ × D_∞` (control) | 4 at levels 1–9 | `U1 -> C2` |
| right-angled pentagon (levels 1–5) | 4 or 5 | `U1 -> C2` (one `C3` at level 1) |
| right-angled hexagon (levels 1–3) | 5 or 6 | `U1 -> C2` (4 per level), `U1 -> C3` (2 per level) |

**Result: PASS, in the weak sense.**
- Every non-matching atom maps exactly onto a union of 2 or 3 atoms at one level. The number is
  bounded and does not depend on the level.
- `C2` is `2^1`, one wall through the point.
- `C3` is not a power of two. So in those cases the image is a union of cylinders at a level where
  one of the four `2^2` pieces is empty, or the two walls are only partly relevant. This is
  consistent with item 1, since cylinders over two walls can have 3 nonempty cells.
- The grid control passes too. So bounded configuration images do not by themselves distinguish
  good hosts from bad ones.

## 3. The repaired engine is the wall engine

The repair adds, as tiles, the images of atoms: cylinders over `g𝒲_n` for all `g` and `n`. By
item 1 these are the Roller cylinders over the wall sets of translated balls.
- **Common refinements are automatic.** Two such tiles meet in a union of cylinders over the
  union of their wall sets. So square filling holds, because the family is closed under
  intersection in finite type.
- **This is the cubical Garside structure.** It is the pointed-cube and Roller structure behind
  `pointed-cube-categories-are-li-garside-categories`, and Cuntz stabilization makes it F_∞
  (`cuntz-stabilized-garside-full-groups-are-f-infinity`).
- **So for cubulated hyperbolic groups the repaired engine exists, and it is the known one.** It
  has the same reach as the 2V route: everything already covered.

**For a Kazhdan hyperbolic group** (property (T), hence property FW, so every action on a CAT(0)
cube complex has a fixed point), walls are unavailable. The repair would need an
**intersection-closed, `G`-invariant family of clopen subsets of `∂_h G`**, containing
neighbourhood bases of shadow translates and having finitely many shapes up to translation and
refinement. Call it a *finite-type tile semilattice*.
- **What complement-closure would force.** A family of halfspaces closed under complement would
  give a cubulation (Sageev), and (T) excludes that in the nontrivial case.
- **What remains open.** Whether a finite-type tile semilattice without complements can exist
  for a (T) group. That is now the precise F_∞ gate for Kazhdan inputs on the Thumann route.

## Lesson for general BH

- **The repaired engine is the cube complex.** The configuration tiles that repair cone matching
  on a reflection group are cylinders over walls. Once repaired, the horofunction engine *is* the
  cube-complex (Garside) engine. So the Thumann-operad route to F_∞ for hyperbolic hosts reaches
  exactly the cubulated inputs, which are already known.
- **For property (T) inputs the missing object is a wall-free finite-type tile semilattice.** It
  must be a `G`-invariant, intersection-closed family of shadow translates with finitely many
  shapes. Walls are the only known source, and (T) forbids them.
- **The finiteness engine must be chosen with (T) in mind.** Hard inputs must avoid Haagerup
  (Sageev-type) structures in their finiteness machinery as well as in their hosts.

## Next

- **Look for a finite-type tile semilattice in the boundary of a (T) hyperbolic group.** One
  candidate: the family of `G`-translates of shadows together with their pairwise intersections.
  Test whether intersections of two translated shadows have boundedly many shapes. That is one
  more bounded test, on a hyperbolic triangle group with (T)-like rigidity, or on a random group
  if one can be coded.
- **Or leave the Thumann route** and look for a different finiteness complex for Kazhdan inputs.
