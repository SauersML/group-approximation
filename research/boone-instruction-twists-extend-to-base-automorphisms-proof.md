---
rg: 2
id: boone-instruction-twists-extend-to-base-automorphisms-proof
kind: route
title: Conjugation by x squared on the amalgam, a swap and a transvection on the free factor
target: boone-instruction-twists-extend-to-base-automorphisms
requires:
  - asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope
---

Direct computation in the claim body: `s -> s x^-2` is an automorphism of
`G_1` carrying `s x` to `s x^-1`, and a swap followed by a transvection on the
free factor `F(Q cup {q})` carries the machine word to its image.  The
embedding into the central tower is the inner-envelope lemma with `D = B x|
F_I`, and the last two Boone letters are already central.
