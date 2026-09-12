---
rg: 2
id: centralizing-d8-word-anchors-relative-row-orientation-proof
kind: route
title: Retract the anchor packet and telescope its wrong-twist commutator to the D8 mark
target: centralizing-d8-word-anchors-relative-row-orientation
requires: []
---

The presentation `(AOR1)` is the direct product `D_8 times C_2`, so the
map fixing `z,j,y` and sending `e` to `1` is a retraction.  This proves the
marked-base and exact-completeness statements.

Using `e^2=1` and the two commutation relations,

```text
ze j ze j=z e j z e j=z j e z e j=z j z e e j=zjzj=y.
```

This proves `(AOR2)--(AOR3)`.  In block form, `[E,J]=1` gives `US=SV`.
Together with `[E,D]=1`, this yields

```text
(UA)S-S(VB)=UAS-US B=U(AS-SB),
```

which proves `(AOR6)` and exact preservation of the row norm.

For `(AOR7)`, replacing the subword `EJ` by `JE`, then `EZ` by `ZE`,
turns `ZEJZEJ` into `ZJZJ`.  Unitary invariance and the triangle inequality
charge the two replacements by `delta_ej` and `delta_ez`; replacing
`ZJZJ` by `Y` charges `delta_y`.  The reverse triangle inequality gives
`(AOR8)`.  Rounding the four involutions, or applying fixed-finite-group
Hilbert--Schmidt exactification, gives the stated dimension-independent
approximate form.
