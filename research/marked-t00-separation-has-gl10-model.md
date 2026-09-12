---
rg: 2
id: marked-t00-separation-has-gl10-model
kind: claim
title: Marked t00 separation remains transverse to the source corner in GL10
artifacts:
  - research/marked-t00-separation-gl10-proof.md
  - experiments/marked_t00_separation_gl10_audit.py
distinct_from:
  native-t00-y1-collision-pays-marked-opnorm: that proves a surviving mark forces a uniform global operator-norm separation between x_78(t_00) and Y_1=x_78(s_0t_00); this keeps that separation exact and shows that the available occurrence table does not localize it to a signed Hecke or selector-source corner.
  row2-parallel-a2-return-diamond-has-gl8-model: that identifies the two same-root occurrences and hence cannot extend to the marked payment packet; this adds two finite root-position vertices, separates the occurrences, and preserves both literal A_2 return paths.
  center-chain-common-source-authenticates-native-covariances: that asks for a positive model-dependent Hecke-source cut with unequal selector rank; this gives an exact marked occurrence model but contains no source projection or compression typing.
---

**ESTABLISHED LOCALIZATION FENCE.**  Retain the globally paid discrepancy
from `native-t00-y1-collision-pays-marked-opnorm`:

```text
T=x_78(t_00),             Y=Y_1=x_78(s_0t_00),
D=TY=x_78((1+s_0)t_00).                                  (MTS1)
```

That claim proves, in every full-presentation operator-norm model,

```text
||T-Y||_op >= (1/4)||z-1||_op.                           (MTS2)
```

Thus the old `GL_8(F_2)` assignment `T=Y` is genuinely forbidden whenever
the mark survives.  The new information in `(MTS2)` is global, however: it
does not say that a spectral direction witnessing `T-Y` lies in the signed
Hecke source or in either selector source reflection.

The complete exact root-occurrence packet still has a finite marked model.
Add two vertices `b,c` to the previous eight-vertex chart and assign

```text
Y=e_(7_0,8_0),             T=e_(b,8_0),
D=TY,                      L=x_67(t_0)=e_(b,7_0).        (MTS3)
```

Then `T!=Y`, and the literal multiplication row

```text
t_0(s_0t_00)=t_00
```

is represented exactly by

```text
[L,Y]=e_(b,8_0)=T.                                      (MTS4)
```

The actual native arm and its two returns use `T`, not `Y`:

```text
x_57(s_1)=e_(10,b),       [x_57(s_1),T]=A_2=e_(10,8_0),
x_67(s_1)=e_(u,b),        [x_67(s_1),T]=R=e_(u,8_0),
x_69(s_1)=e_(u,c),        x_98(t_00)=e_(c,8_0),
[x_69(s_1),x_98(t_00)]=R.                              (MTS5)
```

The constant `w_79(1)` is represented by the simultaneous permutation

```text
(7_0 9)(b c),                                                (MTS6)
```

so it transports both the old prefix path and the new `t_00` path
occurrence by occurrence.

The discrepancy is also attached exactly to the existing marked child.
Writing `q=s_1t_1`, the coefficient identity

```text
q(1+s_0)t_00s_00=q
```

gives the fixed saturation

```text
[[x_67(q),D],x_8k(s_00)]=x_6k(q).                     (MTS7)
```

In the finite model put

```text
x_67(q)=e_(7_1,b),          x_8k(s_00)=e_(8_0,8_1).
```

Only the `T` component of `D` composes with `x_67(q)`, and `(MTS7)` becomes

```text
e_(7_1,8_1),                                                   (MTS8)
```

the old nontrivial marked transvection.  Thus the model does not evade the
payment by killing the mark or collapsing `D`.

All preceding prefix actors, both order-seven heads, the adjacent braid,
the marked-center cell and the parallel `A_2` return diamond remain exact.
The two extra vertices store the paid same-root distinction as a transverse
root-position multiplicity.  No displayed word is a signed-Hecke source
projection, a selector source reflection, or a compression forcing that
transverse direction into either source corner.  Consequently `(MTS2)`
alone does not pay row-two source/return leakage.

The next live occurrence must multiply or compress `D` by an actual
center-chain source word so that its nontrivial component is visible on the
signed Hecke/source carrier.  A global nonzero-root return, even with a
uniform operator-norm floor, does not perform that localization.

This is a scoped model of the displayed ordinary-root occurrence table,
not a representation of the full binary Leavitt elementary group.  The
calculation is in the elementary image and makes no assertion about a
central Steinberg lift.  No Property T, Kazhdan input, trace assumption,
literature theorem, local computation, or Lean compilation is used.

DERIVATION
marked-t00-separation-gl10-proof

