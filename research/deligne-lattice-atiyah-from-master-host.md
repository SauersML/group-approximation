---
rg: 2
id: deligne-lattice-atiyah-from-master-host
kind: route
title: Restrict Strong Atiyah from the master host to Deligne's torsion-free level-3 lattice
target: deligne-torsion-free-lattice-satisfies-strong-atiyah
requires:
  - master-host-satisfies-algebraic-strong-atiyah
  - two-generator-fp-torsion-free-universal-whitehead-container
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
artifacts:
  - research/artifacts/atiyah-permanence-closure-kazhdan-rf-2026-09-16.md
---

## Why sufficient

Fix `n >= 2`.
1. By `deligne-universal-cover-lattice-is-non-rf-kazhdan`, `Sp_2n(Z)` is
   finitely presented and `ker p = Z`.  So `Lambda_n` is finitely presented
   and torsion-free (artifact Section 3: Reidemeister--Schreier, P. Hall's
   lemma, and Minkowski's lemma at level 3).
2. A finitely presented group is countably generated and recursively
   presented.  So `Lambda_n` embeds in the host `E`
   (`two-generator-fp-torsion-free-universal-whitehead-container`, as recorded
   in `master-host-satisfies-algebraic-strong-atiyah`).
3. Strong Atiyah over `Qbar` passes to subgroups.  For `H <= G` and a matrix
   `A` over `Qbar[H]`, `l2(G)` is an orthogonal sum of copies of `l2(H)`
   indexed by cosets, and `r_A` acts by the same operator on each copy.  So the
   spectral measures of `r_A^* r_A` over `N(H)` and over `N(G)` coincide, and
   so do the kernel dimensions.  This is Step 1 of
   `algebraic-atiyah-determinant-colimit-proof`.  So every rank over
   `Qbar[Lambda_n]` is a rank over `Qbar[E]`, which is an integer by
   `master-host-satisfies-algebraic-strong-atiyah`.  `∎`

## Use

This route runs in the direction target => test case.  Its value is
contrapositive: a non-integral rank over some `Lambda_n` refutes the master
host claim.  A proof of the test case would give Strong Atiyah for a group
outside the permanence class `T` of
`atiyah-permanence-closure-kazhdan-subgroups-are-rf`.  None of the proved
classes recorded in this graph reaches such a group.
