---
rg: 2
id: tagged-sheared-diagonal-one-chart-hits-mark-area
kind: claim
title: A direct one-chart filling of the tagged sheared diagonal has unbounded fixed-mark return area
distinct_from:
  tagged-shift-shear-has-unbounded-fixed-mark-area: that uses the explicit coefficient shear carrying the ordinary diagonal to the sheared one; this rules out a direct fixed Steinberg block transporter without passing through that shear.
  tagged-shift-stabilizer-normalization-has-unbounded-row-holonomy: that detects two canonical endpoint-row comparisons; this needs only one sheared row and one tagged column and detects the return of their fixed commutator mark.
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
---

**ESTABLISHED ONE-CHART NO-GO.**  In the tagged binary-Leavitt table put

```text
p_(ij)=c_ic_j=x_12(A_i+A_j),
h_(ij)=x_23(B_i+D_(ij)),
z=x_13(q).                                                (DSD1)
```

The coefficient identity

```text
(A_i+A_j)(B_i+D_(ij))=q                                  (DSD2)
```

makes the sheared diagonal discrepancy

```text
delta_(ij)=[p_(ij),h_(ij)]z^(-1)                         (DSD3)
```

exactly trivial.  Nevertheless it cannot be filled uniformly by taking one
fixed marked Steinberg prototype and supplying all three private addresses
only through one outer conjugator.

Precisely, fix words `p_*,h_*,z` with

```text
[p_*,h_*]=z,                     [p_*,z]=1.              (DSD4)
```

Suppose pair transporters `g_(ij)` simultaneously take the prototype row
and column to `p_(ij),h_(ij)` and return its commutator mark to the literal
fixed mark:

```text
g_(ij)p_*g_(ij)^(-1)=p_(ij),
g_(ij)h_*g_(ij)^(-1)=h_(ij),
g_(ij)zg_(ij)^(-1)=z.                                   (DSD5)
```

Then no constant bounds

```text
Area(g_(ij) z g_(ij)^(-1) z^(-1))                       (DSD6)
```

over the growing address packets.  Consequently `delta_(ij)` cannot be a
literal conjugate of the fixed null word `[p_*,h_*]z^(-1)`, nor can a
factorwise fixed-prototype diagram compare its conjugated terminal mark to
the literal `z` with bounded area.

Indeed, the transporters in `(DSD5)` form infinitely many distinct cosets in
`C_Delta(z)/<z>`.  Finite-mark centralizer-area properness forces `(DSD6)`
to diverge.  This argument does not use the earlier coefficient shear
`1+B_iA_j`; it applies to any direct simultaneous Steinberg
addition/multiplication chart for the rank-one Gram block `(DSD2)`.

The scope is important.  This does not lower-bound the area of `(DSD3)` for
arbitrary diagrams.  A bounded diagram using several independently
conjugated prototype cells could in principle cancel its internal mark seams
without ever filling an individual word `(DSD6)`.  Such a genuinely
multi-chart construction remains open.

No Property `(T)`, Kazhdan input, matrix approximation, trace, or literature
theorem is used.

DERIVATION
tagged-sheared-diagonal-mark-return-proof
