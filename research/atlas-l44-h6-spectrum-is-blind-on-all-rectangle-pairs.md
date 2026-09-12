---
rg: 2
id: atlas-l44-h6-spectrum-is-blind-on-all-rectangle-pairs
kind: claim
title: Every L4(4) H6 rectangle pair has the source order-three spectrum
artifacts:
  - experiments/atlas_a4_l44_fan_escape.py
distinct_from:
  atlas-l44-local-packet-fans-do-not-force-subfield-support: that counts the fan and rectangle escape fibers; this proves the natural H6 module-spectrum filter is constant on the entire rectangle fiber.
  atlas-l44-h6-has-thirty-frobenius-frames: that factors the centralizer fiber after a liftable pair is fixed; this shows characteristic-polynomial data cannot decide which rectangle pairs are liftable.
---

For every one of the `1262` ordered ambient `H6` rectangle pairs surviving
the four bidirectional packet incidences in `GL4(4)`, the product of the two
generating involutions has characteristic polynomial

```text
x^4+x^3+x+1 = (x+1)^2 (x^2+x+1).                    (L44S-1)
```

This is exactly the characteristic polynomial of the source `H6` order-three
element on the scalar-extended natural `A8` module.  Thus the entire rectangle
fiber has the same semisimple `C3` spectrum and fixed-space dimension as the
source module.

Consequently characteristic polynomial, trace, determinant, and the
dimension of the order-three fixed space cannot reduce the `1262` pairs
before the common `H18` placement.  Any liftability filter must see the
nonsemisimple simultaneous `S3` extension data or directly use the thirty
Frobenius forms from `atlas-l44-h6-has-thirty-frobenius-frames`.

