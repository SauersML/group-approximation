---
rg: 2
id: free-factor-isotropy-of-fp-full-subgroups-is-fp
kind: claim
title: If a free factor B of D = A * B is the full isotropy of a point, then every finitely presented piecewise-D group that contains B and moves the point locally retracts onto B, so B is finitely presented
distinct_from:
  fp-stabilizer-engines-need-decidable-vertex-groups: that forces only a solvable word problem on the vertex group of a finitely presented engine; this forces a finite presentation, for any free-factor isotropy, by a retraction.
  shell-envelope-fp-forces-fp-germ-group: that pushes the Schreier complex into the V germ groupoid of one singular orbit of a shell envelope; this uses the free-product normal form, whose germ cocycle has finite support, and ends with a retraction instead of an injectivity check.
  fp-almost-v-groups-have-fp-germ-groups: that concerns groups between V and the almost-V group; this concerns piecewise-D groups for a free product D and any compact totally disconnected D-space.
  relative-automorphism-fp-host-reflects-base-presentation: that is the analogous reflection for the BFFHZ relative automorphism action; this is the reflection for full groups of free-product actions.
---

**ESTABLISHED** by `free-factor-isotropy-germ-cocycle-retraction-proof` (lane proof,
swarm-0917-w12-w12-bh-last1, 2026-09-18; elementary, self-contained; not reviewed).

## Setting

- `D = A * B` is a free product of two groups. `D` acts by homeomorphisms on a compact
  Hausdorff totally disconnected space `X`.
- A homeomorphism `h` of `X` is *piecewise-`D`* if there are a finite clopen partition
  `X = U_1 ⊔ … ⊔ U_n` and elements `d_i ∈ D` with `h|_{U_i} = d_i|_{U_i}`. These form
  the topological full group `[[D ⋉ X]]`.
- `x ∈ X` is a point and `O = D·x` its orbit.

## Theorem

Assume:

- **(H1) Free-factor isotropy.** The stabilizer `D_x` equals `B`.
- **(H2) Germ faithfulness.** No nontrivial element of `B` is the identity on a
  neighbourhood of `x`.
- **(H3) A finitely presented locally moving group.** `E` is a finitely presented
  group of piecewise-`D` homeomorphisms with `B ≤ E` (acting through `D`). For every
  neighbourhood `N` of `x`, infinitely many points `c(x)` arise from elements `c ∈ E`
  that are the identity outside `N`.

Then `B` is a retract of an explicit finitely presented group `Q`. In particular `B` is
finitely presented.

`A` is arbitrary. `B` need not be finitely generated in advance; finite generation
follows.

## Consequences

- **Stabilizer engines.** For the engine `F_B` of `Z/k * B`, every finitely presented
  `E` with `D(F_B) ≤ E ≤ F_B` and `B ≤ E` forces `B` to be finitely presented
  (`stabilizer-engines-force-fp-vertex-groups`). This refutes
  `simple-inputs-have-finitely-presented-stabilizer-engines`, through the non-finitely
  presented decidable simple group `Z V_Z`
  (`regular-cyclic-twisted-core-has-non-fp-stabilizer-engine`).
- **Class kill.** No construction that realizes the input group, or a decidable simple
  envelope of it, as the full isotropy of a free factor inside a finitely presented
  locally moving full group can reach Boone–Higman from a group that is not already
  finitely presented. The envelope `S` must already be a finitely presented group, and
  when `S` is simple it is then itself a finitely presented simple host of the input.
  So such routes are circular: they are never weaker than the conjecture for the input.

## Named invariant and the step where the class dies

The invariant is the **germ cocycle** `β(s, y) = g_{sy}^{-1} λ g_y ∈ B`, taken with
the free-product normal-form transversal `g_y`. For a free factor it has **finite
support** (Step 1 of the proof). Finitely many relator loops therefore present a group
`Q` onto which `B` retracts. Every member of the class dies at the step
"prove the envelope finitely presented", because that step would present the isotropy.

## Lesson for general BH

- Finite presentation of a full group is inherited by the isotropy of a point exactly
  when the germ cocycle at that orbit is finitely supported and the group moves the
  point locally. Free factors give finite support. So hosts in which the input is a
  free-factor vertex group are only as good as a finite presentation of the input.
- Hosts that escape must break finite support: amalgams or HNN extensions over infinite
  edge groups, where normal forms carry an edge element along the whole word. Or they
  must make the input a proper subgroup of the isotropy, or a non-free-factor subgroup
  of `D`.
