---
rg: 2
id: atlas-a4-parabolic-c3-bridge-energy-ceiling
kind: claim
title: The A4 packet and 19243 keep the four-coordinate parabolic-C3 bridge energy at most one sixth
distinct_from:
  atlas-a4-t30-energy-ceiling-below-q14-wall: that asks directly for the transverse t30 covariance ceiling; this isolates the exact four named packet/collision coordinates which imply it through a certified shortest group word.
  atlas-a4-rank-three-core-commutant-collapse: that asks for convergence to the entire GL3(2) commutant; this only asks for a strict weighted energy budget on one H6 letter, one K letter, the central C3 escape, and the collision translation.
---

Let `U_n` satisfy the normalized exact-regular A4 packet hypotheses and
`q_19243(U_n)->1`.  Use the four elements `h,k,z,b` fixed in
`atlas-t30-is-one-parabolic-c3-bridge`, and prove

```text
limsup_n E_PC3(U_n)<=1/6.                              (A4-PC3-CEIL)
```

where

```text
E_PC3(U)=2 delta_U(h)^2+2 delta_U(k)^2
          +delta_U(z)^2+delta_U(b)^2.
```

This is sufficient, not asserted established.  The spherical chord theorem
applied to the exact six-letter bridge improves the Euclidean estimate
strictly at the boundary and gives

```text
limsup_n x30(U_n)^2
 <=2 sin^2(6 asin(1/12))<1/2.
```

Thus no separate compactness argument or extremizer exclusion is needed.
More generally, the same proof closes the q14 contradiction from the weaker
strict ceiling

```text
limsup_n E_PC3(U_n)<24 sin^2(pi/36),
```

whose right-hand side is strictly larger than `1/6`.  The displayed
`1/6` target is retained because it is the natural weighted quadratic budget
suggested by the packet decomposition, not because the bridge needs that
much strength.

The four coordinates have a direct structural meaning.  The first two lie in
the two packet `S3` factors which generate the rank-three core, `b` is the
translation read by collision `19243`, and `z` is the one central `C3`
direction which escapes the affine parabolic.  Thus `(A4-PC3-CEIL)` is a
finite-multiplicity return estimate on exactly the four pieces that the
subgroup ladder proves indispensable; it does not ask for full A8
commutant collapse.

## Attempts

- Work after the `K_(2,2) disjoint_union K_(2,4)` tree gauge.  Match `h` and
  `k` to the two component root gauges, `z` to one of the three large-component
  rectangles, and `b` to the 19243 residual.  The desired constant is the
  weighted sum `1/6`, not exact flatness of all four rectangles.
- The constant `1/6` is allowed.  Spherical curvature of the unitary partial
  products supplies the strict margin which weighted Cauchy--Schwarz loses.
- Do not delete `z`.  The affine-parabolic normal-closure audit proves that
  `h,k,b` alone leave a full `GL_3(2)` quotient and cannot control the
  transverse coordinate.
- Prove the non-strict energy estimate directly.  There is no genuine
  equality configuration to classify: a straight six-chord path with
  positive lengths cannot remain on the unit sphere.
