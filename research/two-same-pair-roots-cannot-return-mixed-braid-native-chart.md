---
rg: 2
id: two-same-pair-roots-cannot-return-mixed-braid-native-chart
kind: claim
title: Two same-pair roots cannot return the mixed-braid residual to the native chart
artifacts:
  - research/two-same-pair-mixed-braid-native-target-proof.md
distinct_from:
  one-elementary-root-cannot-return-mixed-braid-native-chart: that permits one arbitrary root position; this permits two arbitrary-depth roots in both orientations of the residual `(7,9)` channel.
  paired-critical-opposite-roots-return-only-trivially: that treats a pair of reverse roots used as a relative correction to an already valid Whitehead transporter; this treats a pair appended to the asymmetric mixed-braid residual.
  first-cross-whitehead-has-no-alternative-low-depth-return: that treats a second same-pair partial Whitehead after the coarse cross word `K_0`; this treats two unrestricted elementary coefficients after the distinct residual `P`.
---

**ESTABLISHED TWO-ROOT SAME-PAIR FENCE.**  Let `P,J,Q` be the mixed-braid
residual, first native Whitehead, and signed Hecke projection from
`one-elementary-root-cannot-return-mixed-braid-native-chart`.  For arbitrary
binary-Leavitt coefficients `a,b`, let `R_1,R_2` each belong to one of the
two root subgroups

```text
U(a)=x_79(a),               L(b)=x_97(b).              (TRN1)
```

Then

```text
J^(-1)R_2R_1P notin Norm(L_0),                         (TRN2)
```

and consequently

```text
(R_2R_1P)Q(R_2R_1P)^(-1) != JQJ^(-1).                 (TRN3)
```

Same-orientation pairs collapse by root additivity to the already fenced
one-root case.  For the two opposite orders, apply the word before `J` to
`e_7`.  With `P e_7=q_0e_7+q_1e_9`, the `e_9` coefficient after
`U(a)L(b)` is

```text
bq_0+q_1,                                               (TRN4)
```

which cannot vanish: right multiplication by `q_1` would give `q_1=0`.
For the other order `L(b)U(a)`, the `e_7` coefficient is

```text
q_0+aq_1.                                               (TRN5)
```

If the `e_9` coefficient is nonzero, the vector already misses the first
Hecke fixed space.  If it vanishes, applying `J` produces an `e_8`
coefficient

```text
x_1(q_0+aq_1),                                         (TRN6)
```

which is nonzero because its right `q_0` component is
`x_1q_0=x_1`.  Thus `JR_2R_1Pe_7` never lies in
`F_1=<e_2,e_7>_R`, proving `(TRN2)`.

This closes the two-coordinate repair of the shortest mixed-braid
residual at arbitrary coefficient depth.  It does not cover two roots in
different coordinate channels.  The shortest live native-target word must
therefore leave the `(7,9)` block through a genuinely three-coordinate
path (or use at least three further same-pair occurrences).

No Property `(T)`, Kazhdan input, trace hypothesis, stability theorem,
enumeration, literature result, local computation, or Lean compilation is
used.

DERIVATION
two-same-pair-mixed-braid-native-target-proof
