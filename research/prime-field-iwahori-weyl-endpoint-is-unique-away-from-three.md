---
rg: 2
id: prime-field-iwahori-weyl-endpoint-is-unique-away-from-three
kind: claim
title: The standard prime-field Iwahori Weyl endpoint is unique away from characteristic three
distinct_from:
  p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment: that supplies the exact characteristic-three failure; this proves uniqueness when the dilation remains regular semisimple.
  prime-bs14-packet-extension-classification: that classifies which abstract primitive BS packets admit an extension; this classifies the extending group element over one fixed standard finite-field core.
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that is a representation-level uniform HS repair theorem over arbitrary odd congruence quotients; this is only the exact rank-one field calculation which identifies the sole field-level degeneracy.
---

Let `k` be a finite field of characteristic greater than three and work in
`PSL_2(k)`.  For the standard square-free BS core

```text
r=h(2)=diag(2,2^(-1)),       t=u(1)=[1 1; 0 1],       (PFU1)
```

there is exactly one group element `x` satisfying

```text
x^2=1,       xrx=r^(-1),       (xt)^3=1.              (PFU2)
```

It is the standard Weyl element `w=[0 -1;1 0]`.  Consequently the second
Iwahori cubic is unnecessary for **group-element uniqueness on this fixed
field core**.  This statement is not a representation-level stability or
basin theorem: multiplicity commutants and moving congruence rings remain.

The depth extension is now exact:
`prime-power-iwahori-weyl-endpoint-is-unique-away-from-three` proves the
same group-element uniqueness over every `Z/p^kZ`, `p>3`.  Conversely,
`congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits` shows
that even this all-depth uniqueness leaves a large exact endpoint fiber in
the regular representation.

Characteristic three is exactly the exceptional field-level case.  There
`h(2)=-I=1` in the projective group, so the inversion row loses its torus-
normalizer content; `p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment`
exhibits distinct exact endpoints over the same core.  Thus arbitrary-
baseline failure is a fixed local degeneracy, not evidence of a new
moving-conductor family away from three.
