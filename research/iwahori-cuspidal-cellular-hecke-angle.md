---
rg: 2
id: iwahori-cuspidal-cellular-hecke-angle
kind: claim
title: The cuspidal Iwahori angle has the Deligne gap in the native cellular Hodge norm
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-cuspidal-hecke-angle: that proves the same scalar bound in the Petersson norm; this proves it in the fixed cellular quotient norm used by Hilbert--Schmidt cocycles and therefore bypasses cusp-tail comparison.
---

**ESTABLISHED.**  Equip the degree-one cochains of the modular Bass--Serre
orbicomplex and its index-three Iwahori cover with the stabilizer-weighted
sum-of-squares norm, and cohomology with the minimum-representative
(cellular Hodge) norm.  For every finite-dimensional unitary congruence
coefficient module, the two degeneracy maps on cuspidal cohomology satisfy

```text
||res_1 f-res_2 g||_cell^2
 >= (3-2 sqrt(2))(||f||_cell^2+||g||_cell^2).           (CCH1)
```

The constant is independent of congruence level, coefficient dimension,
and deck-group isotypic component.  In particular no comparison between a
compact core and the full Petersson cusp is required.
