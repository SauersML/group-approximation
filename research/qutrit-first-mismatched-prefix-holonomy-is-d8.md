---
rg: 2
id: qutrit-first-mismatched-prefix-holonomy-is-d8
kind: claim
title: The first mismatched Leavitt qutrit holonomy is a finite D8 packet
artifacts:
  - research/qutrit-mismatched-root-holonomy-proof.md
distinct_from:
  qutrit-matched-prefix-router-family-is-one-finite-hnn-chart: that shows matched rectangular equivalences have only scalar potential cycles; this inserts genuinely non-scalar degree-minus-one and degree-plus-one centralizer roots.
  jacobson-d8-polar-has-flat-nine-phase-first-row: that computes a D8 polar in the one-sided residual chart; this derives a new D8 as the relative holonomy between two full-Leavitt prefix equivalences and computes its complete nine-character Hecke graph.
  qutrit-any-finite-router-polar-carries-at-most-half-residual: that gives a trace-capacity bound for arbitrary finite auxiliary routers; this identifies why the most natural normal-generating return still belongs to that finite-packet firewall.
---

Put `h=J^2Z`. Choose the simultaneous `F_2[C]` basis inside the
`16`-dimensional `h`-fixed block so that ten coordinates are trivial
`C`-modules and the other six are three copies of the nontrivial
two-dimensional type killed by `h`. Choose distinct trivial coordinates
`i,k` and a nontrivial coordinate `j`. In the `h`-normal basis define

```text
x=x_(ij)(t_0),          y=x_(jk)(s_0),          a=x_(ik)(1).
```

After conjugating back by the scalar normal-form matrix, all three lie in
`EL_28(L_(F_2)(1,2))` and centralize `h`. They satisfy the exact
Steinberg relations

```text
x^2=y^2=a^2=1,        [x,y]=a,        [a,x]=[a,y]=1.    (QMH1)
```

Thus `D=<x,y>` is exactly `D_8`. The returned scalar transvection
`a` lies in `K=GL_28(F_2)`, centralizes the whole qutrit group `C`,
and normally generates `K`. This is the smallest natural
degree-minus-one/degree-plus-one seam whose commutator returns a
normal-generating scalar root.

Nevertheless it does not close the qutrit Hall flow. For either
`v=x` or `v=y`,

```text
C intersect vCv^(-1)=<h>.                               (QMH2)
```

Writing `p_(alpha,beta)` for the joint character atom with
`J=omega^alpha` and `Z=omega^beta`, the complete Hecke table is

```text
p_(alpha',beta') v p_(alpha,beta) !=0
  iff 2alpha'+beta'=2alpha+beta,
||p_(alpha',beta') v p_(alpha,beta)||_2^2=1/27.         (QMH3)
```

Hence each holonomy root has a complete three-by-three graph inside each
`h`-spectral fibre. It can move leaked mass back to the active
`J`-sector, but it moves the other two equal-capacity cells at the same
time and supplies no oriented support inequality.

Moreover

```text
D intersect K=<a>.
```

All relations above therefore have the finite-amalgam cover

```text
K *_(<a>) D_8  -> <K,x,y> <= EL_28(L).                  (QMH4)
```

The cover is hyperlinear, and its regular finite-vertex models retain
both the uniform nine-character qutrit distribution and the nontrivial
normal-generating mark `a`. In finite-head exactification, the
`h`-spectral multiplicity spaces simply carry a compatible `D_8`
representation. This is the same multiplicity-unitary gauge which
defeats a packet-only Kun--Thom return, here reduced to a finite
involution gauge.

The arrow in `(QMH4)` is not proved injective, so this does not decide
the concrete matrix subgroup. It proves that the displayed mixed-root
relation, its normal-generating commutator, and the entire atom table
still have exact finite-amalgam countermodels. A surviving mismatch must
use an infinite-order centralizer word with a relation not factored
through a finite vertex packet, or a second noncommuting mismatch whose
joint holonomy cannot be represented on the regular multiplicity space.
