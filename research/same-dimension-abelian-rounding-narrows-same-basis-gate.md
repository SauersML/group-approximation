---
rg: 2
id: same-dimension-abelian-rounding-narrows-same-basis-gate
kind: route
title: Use abelian same-dimension stability after bounded-template all-pairs decoding
target: same-basis-rounding-interface-for-sparse-weyl-sampler
requires:
  - finite-abelian-hs-almost-actions-round-in-the-same-dimension
  - bounded-template-all-pairs-additive-decoder
---

Apply the bounded-template decoder separately to the X and Z occurrence
tables to obtain all-pairs approximate actions of `F_2^n` on their original
marked carriers.  The same-dimension abelian rounding theorem then gives
exact additive actions without a flexible enlargement.  Intersect/align the
two marked carriers as supplied by the decoder; the total discarded mass
and squared HS change remain controlled by a dimension-independent modulus.

