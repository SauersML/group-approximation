---
rg: 2
id: kt-single-root-majorana-return-finite-countermodels
kind: claim
title: The two-compressor mixed return with one root row has exact Majorana matrix countermodels
distinct_from:
  kt-single-root-mixed-return-has-exact-finite-countermodels: that uses commuting binary lamps and proves the corresponding projection separation; this Cliffordizes the same finite arithmetic quotient and retains exact anticommutation.
  kt-pointed-clifford-energy-one-compressor-no-go: that refutes the scalar pointed profile after restricting to one compressor; this includes the named A,B mixed return, all finite actor relations, and the actual Majorana anticommutation relation.
  kt-elementary-kazhdan-packet-rounds-base-lamp: that gives the full finite Kazhdan generating packet needed to round a lamp once the actor is exact; this proves why replacing that packet by its one visible root cannot work even with exact Clifford data.
---

Use the `q=2`, `d=3` Kun--Thom pair and the explicit generators

```text
B=I+E_12,             A=C B,
r=e_12(x_1),          h=L r L^(-1)=e_12((x_1x_2x_3)^(-1)),       (KMC1)
```

from `kt-ab-marked-return-is-the-first-mixed-cylinder`.  For every finite
actor window there is a finite-dimensional tracial model containing the
exact finite actor image and a trace-zero self-adjoint involution `c` such
that

```text
[c,r]=1,
d=h c h^(-1),
c d=-d c,
||[c,h]||_2^2=2.                                       (KMC2)
```

The actor trace is canonical on the prescribed window, and every
nonidentity Clifford monomial has trace zero.  Thus all finite actor
relations involving both `A` and `B`, the mixed return `(KMC1)`, its one
visible root-stabilizer row, and the genuine Majorana anticommutation table
are simultaneously compatible with zero matrix defect and maximal pointed
wall energy.

Consequently no dimension-free inequality using only those data can force
the marked Majorana pair to collapse.  The minimal surviving profile must
also impose a finite generating/Kazhdan family of `Gamma`-stabilizer rows,
such as the packet in `kt-elementary-kazhdan-packet-rounds-base-lamp`, and
use their **joint** interaction with the mixed `A,B` return.  This claim says
nothing once that full packet is imposed.

