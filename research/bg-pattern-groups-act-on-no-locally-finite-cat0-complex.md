---
rg: 2
id: bg-pattern-groups-act-on-no-locally-finite-cat0-complex
kind: claim
title: If b a b^-1 = a^2 and t a t^-1 = b in a group acting on a set, and every <a>-orbit is finite, then a acts trivially; so the Baumslag--Gersten group and Higman's group have no action with a (resp. any generator) nontrivial on a locally finite tree or locally finite CAT(0) polyhedral complex
distinct_from:
  baumslag-gersten-equicontinuous-generator-acts-trivially: that treats actions on compact zero-dimensional spaces with equicontinuous a; this treats arbitrary permutation actions in which a has only finite orbits, and the geometric hosts (locally finite trees and CAT(0) complexes, not compact) where ellipticity supplies those finite orbits.
  baumslag-gersten-base-is-elliptic-in-every-tree-action: that shows BS(1,2) fixes a vertex in every tree action of BG, and leaves open whether some faithful locally finite Bass--Serre tree action of a group containing BG exists; this shows none exists.
  finite-index-edge-hnn-embeds-in-fp-simple-group: that derives limits of the Bux--Llosa Isenrich--Wu method from residual finiteness of vertex stabilizers; this kills every locally finite tree host for any group containing the Baumslag--Gersten pattern, cocompact or not, whatever the vertex groups.
  higman-group-embeds-in-no-almost-automorphism-group: that proves the profinite four-cycle lemma and excludes almost-automorphism hosts; this uses the lemma to exclude locally finite trees and locally finite CAT(0) complexes.
artifacts:
  - research/bg-pattern-groups-locally-finite-host-obstruction-proof.md
---

**ESTABLISHED** (short proof from the smallest-prime argument; the permutation
and geometric corollaries are not recorded elsewhere in the graph).

Call a triple `a, b, t` in a group a **BG pattern** if `b a b^-1 = a^2` and
`t a t^-1 = b`. In `BG = < a, t | (t a t^-1) a (t a t^-1)^-1 = a^2 >` the
generators form a BG pattern with `a ≠ 1`.

## Statement

1. **Topological lemma.** Let `T` be a Hausdorff topological group and `a, b, t ∈ T`
   a BG pattern. If `cl<a>` is compact and totally disconnected, then `a = 1`.
2. **Permutation actions.** Let a group `Γ` act on a set `S`, and let `a, b, t ∈ Γ`
   be a BG pattern. If every `<a>`-orbit in `S` is finite, then `a` acts trivially
   on `S`. So in every faithful action of a group containing a BG pattern with
   `a ≠ 1`, the element `a` has an infinite orbit.
3. **Locally finite trees.** In every action of `Γ` on a locally finite tree,
   `a` acts trivially. So no group containing `BG` acts faithfully on a locally
   finite tree, cocompactly or not.
4. **Locally finite CAT(0) complexes.** In every action of `Γ` by cellular
   isometries on a locally finite CAT(0) `M_κ`-polyhedral complex with finitely
   many shapes (for instance a locally finite CAT(0) cube complex, or a finite
   product of locally finite trees), `a` acts trivially.
5. **Higman's group.** Let `H4 = < g_i (i ∈ Z/4) | g_i g_(i+1) g_i^-1 = g_(i+1)^2 >`.
   Every action of `H4` on a set in which each `g_i` has only finite orbits is
   trivial. Every action of `H4` on a locally finite tree, or by cellular
   isometries on a locally finite CAT(0) polyhedral complex with finitely many
   shapes, is trivial.

## Consequences for the Boone--Higman lane

- **Bux--Llosa Isenrich--Wu hosts die for the Baumslag--Gersten pattern.**
  Theorems B, 10.5 and 11.1 of arXiv:2408.05673 need a faithful action on a
  locally finite tree. By item 3 no group containing `BG`, and no group
  containing a BG pattern with `a ≠ 1`, has one. This settles negatively the
  question left open in `baumslag-gersten-base-is-elliptic-in-every-tree-action`:
  there is no group in `BS_G` (finite graphs of groups with commensurable vertex
  groups and finite-index edge groups, so locally finite Bass--Serre trees) that
  acts faithfully on its Bass--Serre tree and contains `BG`, whatever `G` is.
- **Lattice and cube-complex hosts die.** No irreducible or reducible lattice in
  a product of locally finite trees, and no group acting faithfully on a locally
  finite CAT(0) cube complex, contains `BG` or `H4`. This includes the
  Burger--Mozes and Rattaggi finitely presented simple lattices.
- **One-relator groups.** Every one-relator group containing `BG` (for example
  `BG` itself, a Magnus HNN step over `BS(1,2)`) is excluded from all these hosts.
  So the Magnus induction step over a non-free base cannot be realized inside a
  locally finite geometric host; any host must act on its space with `a` having
  infinite orbits, i.e. with non-compact cyclic closures.
- **Where the hosts must live.** Item 2 says that in any type (A) actor
  containing `BG`, the element `a` has an infinite orbit on the permuted set.
  This is consistent with the open hosts `nV` and twisted Brin--Thompson groups,
  where orbits of elements are typically infinite.

## Sharpness

- *The exponent 2 is used exactly once* (Step D of the proof, `ord_p(2) ≥ 2` for
  odd `p`). For exponent 3 the analogue fails: in `SL(2,3) = Q_8 ⋊ C_3` take
  `a = i`, `b = j`, `t` of order 3 with `t i t^-1 = j`. Then `b a b^-1 = i^-1 = a^3`,
  `t a t^-1 = b` and `a ≠ 1`, and all orbits are finite.
- *The stable letter is needed.* `BS(1,2) = < a, b >` acts faithfully on the
  locally finite Bass--Serre tree of degree 3, and `a` is elliptic there.
- *Local finiteness is needed.* `BG` acts faithfully on its own Bass--Serre tree
  (not locally finite), with `a` elliptic.

The proof is `bg-pattern-groups-locally-finite-host-obstruction-proof`.
