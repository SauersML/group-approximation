---
rg: 2
id: atlas-l44-h6-has-thirty-frobenius-frames
kind: claim
title: A marked L4(4) H6 frame has thirty subfield forms and H18 makes the lift projectively rigid
artifacts:
  - experiments/atlas_a4_l44_component_invariants.py
distinct_from:
  atlas-l44-local-packet-fans-do-not-force-subfield-support: that counts local incidence escapes; this quotients the surviving common-conjugator fiber by Frobenius forms and proves projective rigidity after both components are placed.
  atlas-common-u-is-twelve-double-coset-system: that is a unitary multiplicity-space liftability problem; this is exact finite-field descent in GL4(4).
---

Put

```text
A=GL4(2) < G=GL4(4),
K=H6 ~= S3,       L=H18 ~= S3 x C3.                (L44D-1)
```

For the certified packet embeddings, exact commutant calculation gives

```text
                         dim_F4 End       centralizer units in G
K                              5                    540
L                              3                     27
<K,L>=A                        1                      3,             (L44D-2)

                         dim_F2 End       centralizer units in A
K                              5                      6
L                              3                      3
<K,L>=A                        1                      1.             (L44D-3)
```

The three units in the common `F4` commutant are precisely the scalar group
`F4^*`.

Moreover

```text
N_G(A)=F4^* A.                                                    (L44D-4)
```

Indeed, conjugation by a normalizer element induces an automorphism of
`A~=A8`.  After multiplication by an element of `A`, either it centralizes
`A`, hence is scalar by absolute irreducibility, or it induces the outer
graph automorphism.  The latter would identify the natural binary module
with its dual and produce a nonzero `A`-invariant bilinear form.  Elementary
transvections in `GL4(2)` force every coefficient of such a form to vanish.

Fix the marked subgroup `K`.  Its `G`-centralizer moves the standard
subfield chart through exactly

```text
|C_G(K)| / |C_G(K) intersect N_G(A)|
 = 540 / (3*6) = 30                                      (L44D-5)
```

distinct conjugate subfield `A8` frames containing that same marked `K`.
Within each frame there are six marked lifts after quotienting the three
ambient scalars.  Thus the raw projective `H6` centralizer fiber of size
`540/3=180` canonically factors as

```text
30 Frobenius/subfield forms  x  6 internal labelings.       (L44D-6)
```

Finally, once compatible images of both `K` and `L` are fixed, two common
conjugators differ by `C_G(<K,L>)=F4^*`.  Hence the full two-component lift is
unique projectively.

This is the sharp commutant reduction of the `1262` `H6` rectangle pairs.
It does not itself discard any pair: before an `H18` image is placed, the
five-dimensional `H6` commutant genuinely carries all thirty subfield forms.
The next exact screen should therefore test thirty forms and six internal
labelings per simultaneously liftable pair, rather than 540 raw centralizer
elements.

