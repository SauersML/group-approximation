---
rg: 2
id: eight-external-returns-have-no-whitehead-gauge-lock
kind: claim
title: None of the eight external returns supplies a native Whitehead gauge lock
invalidates:
  - external-return-whitehead-commutation-kills-s3
artifacts:
  - experiments/external_return_whitehead_orbit_audit.py
  - research/eight-external-return-whitehead-orbit-proof.md
distinct_from:
  signed-hecke-normalizer-has-eight-external-root-returns: that enumerates the roots preserving the signed pair; this exhausts their images under both literal Whiteheads and both complete Singer heads.
  two-external-return-cell-has-finite-s3-model: that tests one commuting pair and one L0 triangle; this rules out every external root as a direct Whitehead-fixed gauge-lock candidate.
---

**ESTABLISHED EXHAUSTIVE INDEX FENCE.**  Use matrix-root positions
`x_ab(1)=I+E_ab`.  The eight external signed-Hecke normalizers are

```text
(7,4),(8,5),(9,6),(2,7),(4,8),(7,8),(5,9),(8,9).      (EWO1)
```

On the active three-coordinate prefix packets, the two literal
Whitehead/Singer rows are

```text
J_1=(7 8),   t_1=J_1 x_84(1)x_47(1),
J_2=(8 9),   t_2=J_2 x_95(1)x_58(1).                  (EWO2)
```

Direct binary matrix conjugation gives the complete classification:

```text
row 1, fixed external under J_1 and t_1: x_59, x_96;
row 2, fixed external under J_2 and t_2: x_27, x_74.   (EWO3)
```

Every root in `(EWO3)` is disjoint from the corresponding active
Whitehead coordinate pair.  For row 1 the other six images under `J_1` are,
in the order `(EWO1)`,

```text
nonexternal root, L_0, x_96, L_0, nonexternal root,
opposite x_87, x_59, L_0,                              (EWO4)
```

with the repeated fixed entries understood from `(EWO3)`; the executable
artifact records the unambiguous position-by-position table.  Row 2 is
analogous: the fixed roots are `x_27,x_74`, while the roots meeting
coordinates `8,9` go to `L_0`, an opposite root, or a nonexternal position.
Conjugation by `t_i` has the same two fixed external roots in each row;
nontrivial arm factors only turn some remaining root images into
non-root transvections.

This exhausts the smallest possible native commutation lock.  A fixed root
`r` commutes literally with `J_i` and `t_i`, but because it is disjoint from
the active three-coordinate packet its reservoir factor is a spectator.
On successive cuts the exact square says only

```text
G_(k+1)=D_k G_k D_k^(-1),                              (EWO5)
```

not `[D_k,G_k]=1`; the source and target multiplicity charts are different.
The sevenfold return telescopes the chart conjugacies and adds no local
commutation.  Roots which map into `L_0` instead acquire identity target
gauge, and roots which leave the external-root menu do not give a
same-carrier return square.

An exact finite fence is obtained by taking one `S_3` reflection packet for
each row's active Whitehead/opposite-root pair, assigning identity gauge to
the four disjoint fixed returns in `(EWO3)`, and defining all target gauges
by `(EWO5)`.  The stage charts may be closed by a finite seven-cycle
coboundary, exactly as in the established moving-stage gauge model.  Every
literal commutation, `L_0` triangle, Weyl square, and Singer naturality
square is exact, while the active gauges remain

```text
D=(1 2),                  E=(2 3),       DE=(1 2 3).  (EWO6)
```

Thus no relation in the exhaustive eight-root/one-Whitehead menu puts `D`
and `E` in a common commutator or imposes a braid length incompatible with
three.  The next candidate must use a longer word mixing at least two
non-fixed external orbits before returning to the same cut; adding further
fixed spectators cannot close `(ESB2)`.  No Property `(T)`, Kazhdan input,
stability theorem, trace hypothesis, literature result, or local Lean
compilation is used.

## Attempts

- **Use a root fixed by `J_i`.**  The four fixed roots are precisely the
  roots disjoint from the active packet; their squares are covariance
  between different chart multiplicities, not commutation on one chart.
- **Use a root meeting the Whitehead pair.**  The exhaustive table sends it
  to `L_0`, the opposite-root braid already modeled by `S_3`, or outside
  the external-root menu.
- **Use the complete Singer head rather than `J_i`.**  The fixed external
  list is unchanged, and some other images cease even to be root
  transvections.  No new short orbit appears.

DERIVATION
eight-external-return-whitehead-orbit-proof
