---
rg: 2
id: fournier-facio-nonhyperlinear-via-rigid-defect
kind: route
title: The hyperlinear defect criterion excludes every free near representation of the Fournier--Facio group
target: fournier-facio-has-no-purely-singular-free-near-representation
requires:
  - hyperlinear-groups-kill-rigid-compression-defects
  - fournier-facio-group-carries-rigid-defect
  - fournier-facio-hyperlinear-iff-singular-near
---

If every hyperlinear group has trivial rigid defect, then `G` is not
hyperlinear, because its rigid pair `Gamma <= G` has a defect containing
`pi(S)`.  By the established equivalence, a purely singular essentially free
near representation of `G` would make `G` hyperlinear, so none exists.

The route uses property (T) of `G`, and so the second compressor, only through
the rigid pair.  That matches `fournier-facio-one-compressor-subgroup-reduces-to-gamma`:
`<Gamma, t_1>` has no property (T), so it cannot be the ambient Kazhdan group
of a rigid pair, and an argument through it has to prove the stronger
`fournier-facio-compression-subgroup-not-hyperlinear`.
