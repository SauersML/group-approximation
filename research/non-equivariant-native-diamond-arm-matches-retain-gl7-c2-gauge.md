---
rg: 2
id: non-equivariant-native-diamond-arm-matches-retain-gl7-c2-gauge
kind: claim
title: Four non-equivariant matches of the first primed native diamond arms retain the GL7-C2 gauge
artifacts:
  - research/non-equivariant-native-diamond-match-gl7-c2-proof.md
  - experiments/non_equivariant_native_diamond_match_gl7_c2_audit.py
distinct_from:
  first-native-diamond-extension-of-cross-return-has-gl7-c2-model: that leaves a primed native arm to be matched from outside its J-conjugate diamond; this supplies both prefix-square matches and both cross-row returned matches and extends the same finite model.
  reverse-return-has-native-arm-leavitt-diamond: that establishes the two J-equivariant diamonds; this compares the first primed diamond directly with source occurrences not obtained by applying J to its two factors.
  intermediate-native-arm-orbit-cuts-retain-the-return-gauge: that fences spectral cuts of one order-seven orbit; this is a literal ordinary-root occurrence fence before any orbit cut.
---

**ESTABLISHED NON-EQUIVARIANT MATCH FENCE.**  Keep the first native
diamond

```text
A=x_97(t_0),       B=x_76(s_0),
A'=J_1AJ_1^(-1)=x_98(t_00),
B'=J_1BJ_1^(-1)=x_86(s_00).                           (NDM1)
```

There are two direct prefix-square reconstructions of its primed arms which
do not conjugate their inputs by `J_1`.  Put

```text
Q_t=x_78(t_0),              Q_s=x_87(s_0).
```

Then the ordinary Steinberg commutator law gives

```text
[A,Q_t]=x_98(t_0t_0)=A',
[Q_s,B]=x_86(s_0s_0)=B'.                              (NDM2)
```

The same two primed arms also have matches from occurrences authenticated in
the next native row and in the independent positive return.  With

```text
C_2=[x_25(t_1),A_2]=x_28(t_00),
D_2=x_87(s_00),              h_1=x_76(1),
L=x_92(1),
```

one has

```text
[L,C_2]=x_98(t_00)=A',
[D_2,h_1]=x_86(s_00)=B'.                              (NDM3)
```

Thus both primed arms are matched non-equivariantly, and `A'` is matched
literally to the independently returned next-row arm `C_2`.  These matches
still do not read the external native-Whitehead gauge.

Indeed, in the seven-coordinate model of
`first-native-diamond-extension-of-cross-return-has-gl7-c2-model`, write
`e_ab=I+E_ab` and use the vertices `(7_0,9,8_0,7_1,10,8_1,6)`.  Extend the
assignment by

```text
Q_t=C_2=e_(7_0,8_0),       L=A=e_(9,7_0),
Q_s=D_2=e_(8_0,7_0),       h_1=B=e_(7_0,6).           (NDM4)
```

All four commutators in `(NDM2)--(NDM3)` are then the already assigned
matrices

```text
A'=e_(9,8_0),              B'=e_(8_0,6).              (NDM5)
```

Send the literal actor `J_1` to `(j_0,c)` in
`GL_7(F_2) times C_2=<c>` exactly as before, and give every newly named
occurrence trivial `C_2` coordinate.  The new rows contain no occurrence of
`J_1`; its old covariance rows contain it twice.  Hence the central `c`
still cancels from every equation while remaining nontrivial, and the old
marked child `C_1=e_(7_1,8_1)` still survives.

Consequently even the requested non-equivariant primed-arm match, including
the literal cross-row match to `C_2`, admits an exact finite marked model.
The post-fence seam is narrower: a live relation must contain an odd typed
occurrence of `J_1` (for example one of the three literal factors of its
Whitehead word), rather than only reconstructing an output of conjugation by
`J_1`.

This is a scoped occurrence-table model, not a representation of the full
binary Leavitt Steinberg group.  No Property `(T)`, Kazhdan input, stability
theorem, trace hypothesis, literature theorem, or local computation is used.

DERIVATION
non-equivariant-native-diamond-match-gl7-c2-proof
