---
rg: 2
id: atlas-second-core-rectangle-coupling-recreates-collision
kind: claim
title: The second core rectangle closes in GL3 but its canonical coupling recreates the collision involution
artifacts:
  - experiments/atlas_a4_two_core_rectangles_coupling.py
  - research/artifacts/atlas-a4-two-core-rectangles-coupling.json
---

The second `K_(2,2)` component has a faithful exact `GL_3(F_2)` model of
order 168.  Under the fixed packet alignment, its four edge products all have
order three.  The two canonical rectangle groups intersect in `S3` and generate
`A8` of order 20160.

This coupling cannot simply replace the right vertex in the finite collision
carrier.  The collision involution lies inside the second rectangle group.  In
the canonical `A8` coupling the 19243 collision word is exactly that nontrivial
involution, hence has order two rather than being trivial.  Thus the second
rectangle itself is finite and harmless; the first genuine seam is its coupling
to the first rectangle while retaining the collision equation.

For the existing 4032-point carrier there is an earlier marked-order
obstruction: it has `ord(yc)=6` and `<b,y,c>~=S3 x C2`, whereas the canonical
second rectangle has `ord(yc)=3` and `<b,y,c>~=S4`.  Hence that particular
carrier cannot be enlarged injectively through the second rectangle.
