---
rg: 2
id: binary-jacobson-first-mixed-kernel-is-three-syllable
kind: claim
title: A shortest Jacobson relation beyond the complete finite overlap is the three-balanced controlled swap
artifacts:
  - research/binary-jacobson-first-mixed-kernel-relator-proof.md
distinct_from:
  binary-jacobson-three-cycle-is-controlled-swap-and-marked-mf: that multiplies three balanced shifts and proves a smaller common-column subgroup is amenable; this proves the resulting relation is a nontrivial kernel word of minimum balanced-syllable length in the complete finite-overlap envelope.
  binary-jacobson-one-step-finite-type-envelope-is-marked-mf: that constructs the marked virtually free envelope and rules out type-support Hall deficits; this identifies the first explicit relation killed by its quotient onto the full Jacobson elementary group.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for a matrix-coordinate common PI return; this identifies its shortest possible mixed relator but does not assert that the controlled swap authenticates the required intertwiner.
---

**ESTABLISHED.**  Retain `F,h,u,a` and

```text
Gamma_F=F *_K (K x <h>) -> E=EL_3(J)                   (JKR1)
```

from `binary-jacobson-one-step-finite-type-envelope-is-marked-mf`.  Let `r`
be the constant Weyl permutation cycling the three active coordinates,
`1 -> 2 -> 3 -> 1`, and put

```text
a_12=a=h u,
a_23=r a r^(-1),
a_31=r^2 a r^(-2).                                     (JKR2)
```

In `E` their product is the finite-packet element

```text
c=a_31 a_23 a_12
 =[[1,0,0],[0,P,Q],[0,Q,P]] in F,
P=ST=1-Q.                                               (JKR3)
```

Consequently

```text
R_3=(r^2 h u r^(-2))(r h u r^(-1))(h u)c^(-1)          (JKR4)
```

lies in the kernel of `(JKR1)`.  It is nontrivial in `Gamma_F`.  Indeed,
using `r^3=1`, the amalgam normal form of `(JKR4)` is

```text
R_3=r^2 h k h k h u c^(-1),       k=u r^2.              (JKR5)
```

The constant permutation `k` is nonidentity.  The explicit overlap is
`K={(g,1)}` with trivial tail component, whereas every nonidentity constant
permutation has the same nonidentity component in both factors of
`F=G_Q x G_P`.  Thus `k notin K`, and `(JKR5)` is reduced with three
`(K x <h>)\K` syllables.  Bass--Serre normal form proves `R_3!=1`.

This balanced-syllable length is optimal.  There is no nontrivial element of
`ker(Gamma_F -> E)` representable with at most two occurrences of `h`:

* length zero lies in the vertex copy of `F`, on which the map is the
  identity;
* a length-one kernel word would imply `h in F`;
* if `f_0 h f_1 h f_2` maps to one, then `h f_1 h in F`, so by the definition
  `K=F cap hFh` one has `f_1 in K`.  The word therefore reduces in
  `Gamma_F` to an element of `F`, and injectivity on `F` makes it trivial
  already in `Gamma_F`.

Even adjoining this optimal relator does not kill the mark.  Under
`F=G_Q x G_P`, put

```text
t=(1,u) in F.                                             (JKR6)
```

The element `t` is an involution and centralizes
`K={(g,1)}`.  Hence the identity on `F` and `h |-> t` define a retraction

```text
Gamma_F/<normal closure of R_3> -> F.                    (JKR7)
```

Indeed `a=hu` maps to the head-only Weyl element `(u,1)`.  Its three cyclic
conjugates multiply to `(w_23,1)`, which is exactly the head/tail
decomposition of `c` in `(JKR3)`.  Thus `(JKR7)` is well defined and retains
the nontrivial mark `w`.

Thus the minimum possible positive balanced-syllable length beyond all finite
type data is three, and `(JKR4)` realizes the bound.  Its
coefficient content is precisely the simultaneous use of `TS=1` and
`ST=P=1-Q`: three cyclic balanced rows cancel their Laurent shifts but leave
the head-controlled swap `(JKR3)`.  This is the first finite mixed holonomy
that a Jacobson selector may exploit.  The sibling relation
`binary-jacobson-shortest-affine-braid-is-finite-marked` shows that the
minimum relation is not unique.  The finite retraction `(JKR7)` proves
that the identity `(JKR3)`, even together with the entire packet and complete
one-step overlap, is not yet the desired PI or Hall authentication.  A
successful proof must couple this first mixed cell to at least one further
occurrence which destroys the head/tail retraction.

DERIVATION
binary-jacobson-first-mixed-kernel-relator-proof
