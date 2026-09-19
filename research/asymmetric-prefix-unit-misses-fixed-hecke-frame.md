---
rg: 2
id: asymmetric-prefix-unit-misses-fixed-hecke-frame
kind: claim
title: The asymmetric prefix conjugacy leaves the fixed Hecke and Singer frames
artifacts:
  - research/asymmetric-prefix-unit-hecke-frame-proof.md
distinct_from:
  asymmetric-prefix-unit-conjugates-native-whiteheads: that constructs the exact external conjugacy and its moved-source Grams; this computes the moved quarter signs and proves that diagonal-torus extensions cannot return them to the fixed signed source.
  mixed-whitehead-cell-moves-signed-source: that detects source movement by a signed-subgroup intersection calculation for a different endpoint/native product; this identifies the first literal root-position obstruction for the asymmetric prefix unit.
  full-q-quarter-stabilizer-profile-has-cross-kernel: that is an internal finite-parabolic multiplicity profile; this is a coefficient-level full binary-Leavitt fence outside that quotient.
---

**ESTABLISHED FIXED-FRAME FENCE.**  Retain the asymmetric prefix unit and
ordinary conjugator

```text
u=s_00t_0+s_01t_10+s_1t_11,
D=h_(8,10)(u)h_(7,11)(u),
G=PD,
P:(7 8 9),                                             (AUF1)
```

from `asymmetric-prefix-unit-conjugates-native-whiteheads`.  For the two
literal quarter signs

```text
r=x_58(a_2),       a_2=s_1t_00,
l=x_69(a_3),       a_3=s_1t_000,                      (AUF2)
```

one has

```text
GrG^(-1)=x_59(a_3)=:t_3,
GlG^(-1)=x_67(a_3)=:omega_3.                          (AUF3)
```

The first equality uses the genuinely asymmetric coefficient identity

```text
a_2u^(-1)=a_3.                                        (AUF4)
```

Thus the moved quarter source `F'=GFG^(-1)` is not the original fixed
signed packet occurrence.  The root position `(5,9)` in `t_3` is absent
from the directed root-position closure of

```text
<L_0,r,l>,
L_0=<H,d,f,c,k,v,w,s>.                                (AUF5)
```

The second image also separates this occurrence from all already named
native/Singer translates:

```text
J_1:l |-> l,          J_2:l |-> s=x_68(a_2),          (AUF6)
```

whereas `G:l |-> omega_3=x_67(a_3)`.  The row-two Singer head acts only on
the coordinate block `{5,8,9}` and hence fixes `omega_3`; the row-one head
acts only on `{4,7,8}`, so every image of `omega_3` has its column in that
set and cannot return to column `9`.  Consequently `F'` is not a literal
translate of `F` by any power of either established Singer head.  The bare
Hecke words

```text
u_1=B_2A_1,             u_2=B_3A_2A_1                 (AUF7)
```

fix `omega_3` rootwise and do not supply a return either.

Nor can the fixed-frame defect be repaired by extending the torus `D` to
more coordinates.  Any such extension is diagonal and therefore leaves
the root-position permutation unchanged.  Since conjugating `J_1` to
`J_2` forces

```text
P(7)=8,                   P(8)=9,                     (AUF8)
```

and preservation of the directed center chain
`6 -> 5 -> 4 -> 2` fixes its four vertices, every such extension still
sends the root position `(5,8)` of `r` to `(5,9)`.  Multiplication by units
can change the nonzero coefficient but cannot move or kill this root
position.  Hence no diagonal-torus extension of the candidate can normalize
the displayed signed quarter-source occurrence while retaining
`GJ_1G^(-1)=J_2`.

This is an occurrence fence, not a claim that the two analytic projections
must be different in every specialized representation.  It proves that the
new exact mixed square does not itself provide the fixed-frame ordinary
word identity needed for APG1.  A continuation must add a genuinely
nondiagonal return which moves `(5,9)` back into the signed source while
also cancelling, rather than transporting, the asymmetric-unit reservoir
gauge.

No Property `(T)`, canonical trace, computation, or literature theorem is
used.

DERIVATION
asymmetric-prefix-unit-hecke-frame-proof
