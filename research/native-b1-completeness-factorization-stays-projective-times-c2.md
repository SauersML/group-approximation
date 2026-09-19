---
rg: 2
id: native-b1-completeness-factorization-stays-projective-times-c2
kind: claim
title: The shortest nonzero completeness incidence with the native B1 arm still splits as projective times C2
artifacts:
  - research/native-b1-completeness-projective-split-proof.md
distinct_from:
  single-root-completeness-attachments-are-exhausted: that classifies the abstract one-root incidence types and gives finite models for them; this realizes the shortest composable type with the literal coefficient of the named B1 Hecke arm and extends the mark-positive zero-full-Hecke-source profile.
  intermediate-fold-arm-has-finite-s6-model: that authenticates an abstract propagated arm and one transport inside S6; this identifies the propagated output exactly with the existing B1 occurrence and shows the complementary branch is an orthogonal C2 factor of a literal projective head.
  native-opposite-arm-return-has-finite-s6-model: that uses the uncancelled s0 and t0 arms and an opposite partial Whitehead; this uses the already named b1=s0t1 arm and proves the first nonzero p/native-Hecke incidence is still source-free before any opposite return.
  star-attached-completeness-fold-splits-off-p-corner: that attaches the q child itself to the star center and finds that the p opposite-root corner splits off; this attaches the p child nontrivially to the named B1 arm and finds that the complementary q root splits off.
---

**ESTABLISHED SHORTEST NATIVE-INCIDENCE FENCE.**  Put

```text
p=s_0t_0,             q=s_1t_1,             b_1=s_0t_1
```

in the binary Leavitt algebra, and use one fresh Steinberg coordinate `10`:

```text
P=x_(7,10)(p),        Q=x_(7,10)(q),        N=x_(7,10)(1),
B'=x_(10,2)(b_1),     B_1=x_72(b_1),
A_1=x_47(s_1t_0),     C_1=x_42(q).                         (NBC1)
```

The coefficient equations give the literal ordinary-word table

```text
PQ=N,
[P,B']=B_1,           [Q,B']=1,             [N,B']=B_1,
[A_1,B_1]=C_1.                                          (NBC2)
```

Thus the complementary `p` branch has a genuinely nonzero composable
incidence with a named native Hecke arm: it produces the **same literal**
`B_1` occurrence used by the first anchored q-star cell, and then the named
`A_1` occurrence returns it to the star center.  The `q` child is the crossed
zero branch.  No analytic occurrence identification is being made.

This is shortest in root incidence.  The completeness row already occupies
one root position.  A nonzero ordinary composition needs at least one
additional composable root position; `B'` is that one root, and `(NBC2)`
achieves the desired named output.

Nevertheless `(NBC2)` does not force positive full-Hecke source.  Give
coordinates `7` and `10` the projective label `0`.  Then `P`, `B'`, `B_1`,
`A_1`, the whole marked q-star packet, and both adjacent prefix Whiteheads
lie in one literal projective `SL_10(F_2)` head.  In the canonical elementary
image the remaining root `Q` is supported on the orthogonal q corners at
coordinates `7,10`; it centralizes that entire projective head and generates
one extra `C_2` factor.  Hence the elementary image of the displayed packet
is

```text
SL_10(F_2) times C_2.                                   (NBC3)
```

Tensor the natural permutation representation of `SL_10(F_2)` on its
`1023` nonzero vectors with the two-dimensional regular representation of
that `C_2`.  All rows in `(NBC2)`, the marked-star cells, and the native
Whitehead packet are exact; `P,Q,B'` are nontrivial; and

```text
rank(P_z)=2*256,             rank(E)=2*64,
rank(F)=0.                                                (NBC4)
```

Therefore even the first nonzero `p`-to-native-Hecke composition leaves the
surviving marked/star profile disjoint from the full-Hecke source.  The next
eligible occurrence must prevent the complementary `Q` root from living on
the unused q subcorners of the two `0`-labelled coordinates.  Equivalently,
it must return that complementary branch to a q-labelled native coordinate,
or use an opposite/mixed row which couples those q subcorners to the signed
source.  Merely naming the nonzero `p` output as `B_1` does not do so.

This is a finite packet fence, not a representation of the full infinite
Steinberg group.  No Property `(T)`, canonical trace, literature theorem, or
computation is used.

DERIVATION
native-b1-completeness-projective-split-proof
