---
rg: 2
id: ptfree-sep7-jacobson-packet-escapes-finitary-shift
kind: claim
title: The full Jacobson packet and balanced involution escape the finitary Whitehead shift subgroup
invalidates:
  - binary-jacobson-joint-shortest-cells-finite-model-proof
distinct_from:
  binary-jacobson-finitary-whitehead-shift-is-marked-lef: that establishes LEF for the finitary kernel with one balanced translation; this computes the symbols of the proposed additional packet and proves that it is not contained in that subgroup.
  binary-jacobson-active-cycle-generates-rank-three: that proves generation of the whole rank-three Jacobson group; this identifies the false finitary inclusion used to claim finite marked models for the joint shortest cells.
artifacts:
  - research/artifacts/ptfree-sep7-jacobson-symbol-audit.md
---

Let `J=F_2<S,T | TS=1>`, `Q=1-ST`, and let

```text
sigma: EL_5(J) -> EL_5(F_2[z,z^(-1)])
```

be the symbol map. Write `L=ker(sigma)` for the finitary kernel. In the
first three coordinates put

```text
F=EL_3(F_2[Q]) = G_Q x G_P,
u=w_12(1),
a=[[S,Q,0],[0,T,0],[0,0,1]],
h=a u,
H=<L,a>.
```

Then, with the displayed matrices extended by the identity on the last two
coordinates,

```text
sigma(F)=EL_3(F_2),
F cap L=G_Q,
sigma(u)=w_12(1) != 1,
sigma(a)=diag(z,z^(-1),1),
sigma(h)=[[0,z,0],[z^(-1),0,0],[0,0,1]].
```

In particular, `F` is not contained in `L` or in `H`, `u` is not in `L`,
and `h` is not in `H`. Thus `<F,h>` is not contained in `H`.
In fact the active-cycle generation theorem gives `<F,h>=EL_3(J)`.

These exact calculations invalidate the proposed LEF proof of
`binary-jacobson-joint-shortest-cells-have-a-finite-marked-model`, which
depends on the opposite inclusions `F<=L`, `u in L`, and `<F,h><=H`.
They do not refute the existence of a finite marked model for the two
specific cells; that assertion needs a different proof or an explicit
model. No Property-(T)-free MF collapse follows from this correction.
