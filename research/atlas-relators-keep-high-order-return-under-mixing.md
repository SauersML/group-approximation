---
rg: 2
id: atlas-relators-keep-high-order-return-under-mixing
kind: claim
title: The six Atlas relators keep unit high-order return after every syllable leaves both charts
distinct_from:
  atlas-six-relator-leavitt-tracial-countermodel: that gives an exact positive-five-row-energy model in the Leavitt factor; this additionally makes every individual relator syllable have zero conditional return to either original A8 chart while the complete relator correlation remains one.
  atlas-map-enemy-has-icc-weak-mixing-factor: that conditionally reduces a CE enemy to an ICC weak-mixing factor; this gives an unconditional non-CE factor model proving that weak mixing, normal generation and the six exact relators are mutually compatible.
  atlas-full-relator-data-factor-through-double-commutant-gauge: that concerns left-right multiplicity gauges of one relative chart unitary; this concerns simultaneous inner conjugation of both chart algebras away from their original finite-dimensional positions.
  atlas-radius-nine-packet-gram-sos-is-tracial: that semantically fences universal tracial Gram certificates; this exhibits the exact conditional-expectation correlation pattern responsible for the failure.
  atlas-six-relator-factor-retains-half-nontrivial-s3-mass: that computes positive S3 channel mass in the fixed Leavitt chart frame; this shows that moving the whole frame off both original charts leaves all high-order relator correlations exact.
---

**ESTABLISHED NO-GO.**  Let `Q=L_(F_2)(1,2)^x`, let `M=L(Q)`, and let

```text
A_i=L(A8_i) inside M,             i=1,2,
```

for the two marked Atlas charts.  Write each of the six literal relators as
a reduced alternating chart word

```text
r=x_1 x_2 ... x_m=1,
```

where the respective syllable lengths are

```text
m=6,8,8,8,8,16
```

for `s_0,s_11,s_30,s_44,s_55,c_19243`.

There is a group element `g in Q` such that, simultaneously for every
syllable `x_k` occurring in all six words and both charts,

```text
E_(A_i)(lambda(g x_k g^-1))=0,              i=1,2,    (AHR1)
```

but for every complete relator and both `i`,

```text
E_(A_i)( product_(k=1)^m lambda(g x_k g^-1) )=1.      (AHR2)
```

Indeed the product in `(AHR2)` is exactly

```text
lambda(g r g^-1)=1.                                   (AHR3)
```

Thus the six relations are unit **high-order diagonal correlations** even
when every one-letter chart return is zero.  Conditional expectation cannot
be distributed across their products.

The identical conclusion holds in the centerless ICC quotient
`Lambda_bar` supplied by `atlas-map-enemy-has-icc-weak-mixing-factor` if the
hypothetical CE enemy exists.  Thus `(AHR1)--(AHR3)` are not merely a
non-CE pathology: they are the forced conditional-expectation shape of the
weak-mixing CE branch itself.  The Leavitt model proves unconditionally that
this shape is algebraically and factorially consistent.

The ambient model simultaneously has all of the proposed structural
rigidity:

- `Q` is infinite simple, minimally almost periodic and ICC;
- `M` is a diffuse II1 factor and its adjoint representation on
  `L2(M) minus C1` is weakly mixing;
- every nonidentity chart transvection normally generates `Q`;
- both chart restrictions have their regular characters; and
- all six relators vanish while the intrinsic five-row element `h_5` has
  positive trace.

Therefore no contradiction can follow from the conjunction

```text
exact six relators
+ factoriality and adjoint weak mixing
+ regular finite A8 charts
+ normal generation by the marked transvection.
```

The missing input must distinguish Connes embeddability from the canonical
Leavitt factor.  In particular, weak mixing only separates a moved chart
from the original chart; it preserves all correlations internal to the
simultaneously moved tuple.  Normal generation does not change this diagonal
conjugation covariance.
