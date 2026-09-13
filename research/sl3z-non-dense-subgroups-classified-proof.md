---
rg: 2
id: sl3z-non-dense-subgroups-classified-proof
kind: route
title: Sort the identity component of the Zariski closure by solvability and irreducibility
target: sl3z-non-dense-subgroups-classified
requires: []
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part1.md
---

Let `G°` be the identity component of the Zariski closure of `H`. It is
defined over `Q`, normalized by `H`, and `[H : H ∩ G°]` is finite.

1. **Solvable.** If `G°` is solvable, then `H ∩ G°` is a solvable subgroup
   of `GL_3(Z)`. By Mal'cev it is polycyclic, which gives (V).
2. **Semisimple type.** Otherwise a Levi subgroup has type `A_1`. Type `A_2`
   would force the closure to be `SL_3`, and two simple factors cannot act
   faithfully in dimension 3. So `C^3` is the irreducible 3-dimensional
   module or `2 ⊕ 1`.
3. **Irreducible.** Suppose `G°` acts irreducibly.
   - The unipotent radical has a nonzero invariant fixed space, so it is
     trivial.
   - The central torus centralizes an irreducible action, so it is scalar,
     hence trivial.
   - So `G° = SO(q)`, with `q` unique up to scalars and so rational.
   - `N(SO(q)) = SO(q) × μ_3`, and the nontrivial cube roots of unity are not
     rational. So `H <= SO(q)(Q)`, discrete in `SO(q)(R)`.
   - A definite `q` gives a finite `H`, which is (V). Otherwise (F).
4. **Reducible.** The composition factors have dimensions 2 and 1.
   - Two invariant planes, or two invariant lines, would force three
     one-dimensional factors. So the invariant subspace `U` is unique in its
     dimension.
   - The variety of such subspaces is a single point defined over `Q`, so `U`
     is rational.
   - `H` normalizes `G°`, so `H` preserves `U`. That is (P).

This is Theorem 3.1 of the artifact.
