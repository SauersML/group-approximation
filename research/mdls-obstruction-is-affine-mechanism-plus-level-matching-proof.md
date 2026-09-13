---
rg: 2
id: mdls-obstruction-is-affine-mechanism-plus-level-matching-proof
kind: route
title: Steps 2 and 3 of Magee-de la Salle use only subgroups of the affine group; Step 1 only produces the primitive character
target: mdls-obstruction-is-affine-mechanism-plus-level-matching
requires: []
artifacts:
  - research/artifacts/sl3z-pmf-affine-reformulation-2026-09-13.md
---

Artifact, Section 4.  The source is arXiv:2312.03220v2, Sections 2.3--2.4, read
from the PDF on 2026-09-13.

1. **Step 2 (Section 2.3).**  Move `xi` to `(0,0,1)` with `SL_3(Z/p^r)`, which is
   transitive on vectors that are nonzero mod `p`.  The `xi`-isotypic space `V_chi`
   of `U_1 = (Z/p^r)^3` is invariant under the stabilizer `G_1` and under the
   Heisenberg group `H = {[x;y;z]}` (entries `(2,3)`, `(3,4)`, `(2,4)`).  On
   `V_chi`, `z` acts trivially.  Decompose under `U_2` (entries `(1,3)`,
   `(2,3)`), and conjugate by the coordinate-`(1,2)` copy of `SL_2`.  This gives
   `v` with `x` acting trivially and `y` acting by `exp(2 pi i y / p^r)`
   (MdlS display (2.4)).  All of these groups lie in `P_r`.
2. **Step 3 (Section 2.4).**  `v` is fixed by `N = {(2,3) entry}`.  Under
   `G_2 = SL_2(Z/p^r)`, the translates `g v` are eigenvectors of the group
   `{[0;y;z]}` with characters whose stabilizer is exactly `N`.  So
   `span G_2 v = Ind_N^(G_2) triv`, which contains the trivial representation by
   Frobenius reciprocity.  All of these groups lie in `P_r`.
3. **Step 1 (Section 2.2)** is used by MdlS only to conclude that
   `C_14 = <I + p^(r-1) e_14>` is not in the kernel.  That is exactly the
   hypothesis `xi != 0 mod p` here.
4. **Tensor factors.**  By the Chinese remainder theorem an irreducible
   representation of `(Z/M)^3 x| SL_3(Z/M)` is `(x)_p tau_p`.  `G_2(Z/M)` is the
   product of the `G_2(Z/p^(r_p))`, so its invariants are the tensor product of
   the factors' invariants.  A factor on which `U_1` acts trivially is a
   representation of `SL_3(Z/p^b)` pulled back.  Deligne's representations
   (MdlS Example 2.2, conjugated to coordinates `2,3`) have no invariants for
   this `SL_2`, so such a tensor product can have none.
