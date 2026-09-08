---
rg: 2
id: finite-coset-intersection-elimination-proves-guard-transfer
kind: route
title: Isolate surjunctive coset classes and cancel them through a finite intersection poset
target: surjunctive-guard-subgroups-force-surjectivity
requires: []
artifacts:
  - research/artifacts/gottschalk-surjunctive-guard-finite-intersection-proof-2026-09-08.md
---

The linked artifact gives the complete proof, including the finite
coset avoidance lemma and each uniform inverse assertion.

For a nonuniform local map with finitely many coset masks, all retained
mask stabilizers remain nonempty intersections of the original finite
family. Their commensurability classes form a finite poset under
B<=_a C when [B:B intersect C] is finite. Choose the largest present
class in a fixed linear extension and intersect its stabilizers to L.

Neumann's finite-coset avoidance argument isolates that class while
preserving a common local recovery radius. The isolated map fixes
its exterior and is a finite-track CA over L on the zero-exterior
fiber. Surjunctivity passes to L from the original stabilizers, so
this fiber is bijective. Finite-output perturbation, density, and
compactness give bijectivity for every exterior configuration and a
uniformly local inverse.

Cancel the isolated map. The residual fixes the complement of the
original nonselected masks. Intersecting all remaining selected-class
masks with that set introduces only strictly smaller classes in the
fixed finite poset. The largest present index decreases. Induction
terminates at identity and proves the finite-mask map bijective.

For the target, restrict F to a finite union of H-cosets by zero
filling the exterior and preserving the exterior coordinates of the
new map. Its masks have stabilizers conjugate to H. The uniform local
inverse radius of F transfers to this restriction because both
zero-filled images vanish outside those cosets. Apply the finite-mask
theorem. Every finitely supported target is then attained; compactness
gives surjectivity on the whole full shift. The artifact also proves
the stated finite-memory reduction to H_0.
