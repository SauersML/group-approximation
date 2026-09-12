---
rg: 2
id: iwahori-zero-uniform-angle-from-weil-boundary-proof
kind: route
title: Exactify both cubic triangles next to the compressed even-Weil BS point
target: iwahori-two-loci-have-zero-uniform-angle
requires:
  - even-weil-fixed-line-compression
  - iwahori-two-triangle-torsion-normal-form
  - bs14-two-cubic-strict-repair-constants-diverge
  - projective-dihedral-factorization-has-explicit-hs-retraction
---

Take the compressed tuple from `even-weil-fixed-line-compression` and put
`T_p=S_p^2`, as in the equivalent square-free presentation.  Its BS,
involution, and reflection rows are exact, so
`z_p=(X_p,R_p,T_p) in D_d`.  Its two square-free cubic residuals are
`O(p^(-1/2))` by the fixed word substitutions.

Apply the explicit two-triangle rounding of
`iwahori-two-triangle-torsion-normal-form`.  It changes the square-free tuple
by `O(p^(-1/2))` in the same
dimension and makes both cubic rows exact.  Call the result `y_p`; then
`y_p in C_d` and the first line of `(IZL4)` holds.

The strict separation part of `even-weil-fixed-line-compression`, repackaged
in `bs14-two-cubic-strict-repair-constants-diverge`, gives a universal
`c>0` such that `z_p` is at least `c` from every exact same-dimensional
Iwahori tuple.  But `D_d intersect C_d` is exactly that extension variety,
so the second line of `(IZL4)` follows.  Substitution into `(IZL3)` gives
`c<=L O(p^(-1/2))`, impossible for fixed `L`.

If an alternating-retraction algorithm had uniformly linear step movement
and a uniform geometric contraction on all sufficiently small-residual
points, starting at `z_p in D_d` and first moving to `C_d` would give a
convergent geometric path of total length `O(||z_p-y_p||_2)`.  Its limit
would lie in the intersection and contradict `(IZL4)`.  This proves the
algorithmic consequence without making any claim about local angles inside
one fixed endpoint stratum.
