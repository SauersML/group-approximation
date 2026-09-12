---
rg: 2
id: fp-surjunctive-nonsofic-group-exists
kind: claim
title: A finitely presented group is surjunctive and nonsofic
root: true
distinct_from:
  surjunctive-nonsofic-group-exists: that asks for a finitely generated witness; this supplies a finitely presented witness and controls the full unstable Steinberg kernel needed for its finite presentation.
  kt-pair-group-double-is-nonsofic: that gives nonsoficity of the double family; this fixes a stable-rank example and also proves finite presentation and full nonlinear surjunctivity.
artifacts:
  - research/artifacts/fp-surjunctive-nonsofic-double-2026-09-11.md
---

There exists a finitely presented group that is surjunctive and nonsofic.
One fixed witness is

```text
R_plus=F_2[x_1,x_2,x_3],
R=F_2[x_1^+-1,x_2^+-1,x_3^+-1],
Gamma=EL_6(R_plus),
G=EL_6(R) semidirect SL_3(Z),
D=G *_Gamma G,
```

with the actor acting by monomial substitutions.

The stability range `6=dim(R)+3` identifies
`ker(St_6(R)->EL_6(R))` with `K2(R)=Z^3`. This gives finite
presentation of `EL_6(R)` from the finitely presented Steinberg
source. The actor is finitely presented, and the polynomial edge
group is finitely generated, so the double is finitely presented.

The actor is residually finite. Its double is surjunctive by the
faithful-vertex fold theorem and nonsofic by Kun--Thom Theorem A.

Thus surjunctivity does not characterize soficity even within the
finitely presented groups. The universal Gottschalk conjecture is
not settled by this example.
