---
rg: 2
id: titz-witzel-kernel-sofic-via-flat-hitting-covers
kind: route
title: Flat-hitting sparse branched covers of the Titz--Witzel complex are fully branched, hence make the simple kernel sofic without any hyperbolic-group input
target: titz-witzel-kernel-sofic
requires:
  - titz-witzel-flat-hitting-sparse-branched-covers
  - sparse-fully-branched-covers-iff-sofic-simple-residual
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

**OPEN (two open prerequisites: `titz-witzel-flat-hitting-sparse-branched-covers`
and `sparse-fully-branched-covers-iff-sofic-simple-residual`).**  The second was
proposed as established in swarm-0917 and set back to OPEN after refereeing: its
Step B imports a reduction that needs every vertex link of `Y` to be connected,
a hypothesis nobody had stated.  The links of `Y_1^2` are connected, so the
repair is expected to cost this route nothing, but it has not been carried out.

1. `titz-witzel-flat-hitting-sparse-branched-covers` gives finite branched
   covers `X_k -> Y_1^2` with `beta(X_k) -> 0` satisfying (H).
2. (H) excludes unbranched components.  Such a component is a genuine
   cover, so its universal cover is the `C~_2` building, whose apartments
   immerse flat `R`-disks into `X \ B` for every `R`.  So every `X_k` is
   fully branched.  This is Step D of
   `sparse-fully-branched-covers-iff-sofic-proof`.
3. The finite residual of `pi_1(Y_1^2)` is infinite simple of finite index
   (`titz-witzel-simple-kazhdan-cat0-lattices-exist`).  By
   `sparse-fully-branched-covers-iff-sofic-simple-residual` (2 => 1), it is
   sofic.

**Comparison with `titz-witzel-kernel-sofic-via-branched-hyperbolization`.**
That route has the same hole plus a second independent one: soficity of the
hyperbolic groups `pi_1(X_k)`, which is open in general.  Here that second
hole is gone, and so is the girth condition (G).  Once step 3's prerequisite is
repaired, the flat-hitting cover problem is the last missing piece on this
route.

**Honest weakening available.**  Step 2 uses only that no component is a
genuine cover.  So (H) can be replaced by anything with that effect, for
instance:
* a single branch vertex in each component;
* branched components carrying a fixed fraction of the sheets.

The combinatorial target is therefore strictly weaker than the flat-hitting
claim.  It asks for sparse branched covers of `Y_1^2` in which a positive
fraction of the sheets lies in components that are not copies of `Y_1^2`
or of its genuine double cover.
