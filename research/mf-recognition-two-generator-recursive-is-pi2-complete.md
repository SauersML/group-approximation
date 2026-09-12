---
rg: 2
id: mf-recognition-two-generator-recursive-is-pi2-complete
kind: claim
title: MF and LEF recognition are Pi-zero-two complete already for two-generator recursive presentations
distinct_from:
  mf-recognition-recursive-presentations-is-second-level-complete: that uses countably generated presentations and a countable free product; this reaches two generators, which is optimal, and covers LEF as well as MF.
  mf-recognition-finite-presentations-is-pi2-complete: that reaches finite presentations through a Mikhailova benign witness and tensor-synchronized rope; this result stops earlier at finitely generated recursive presentations and needs no finite-presentation compiler.
---

ESTABLISHED.  For recursive presentations on **two** generators,

```text
MF_rec2   is Pi^0_2-complete,     NONMF_rec2  is Sigma^0_2-complete,
LEF_rec2  is Pi^0_2-complete,     NONLEF_rec2 is Sigma^0_2-complete.   (TG1)
```

Two generators is optimal: a one-generator recursively presented group is
cyclic, hence MF and LEF, so both problems are trivial there.

The hardness reduction is one computable map `e -> P_e` with

```text
e in INF  =>  P_e ~= B2(1)  is residually finite (so LEF and MF),
e in FIN  =>  P_e ~= B2(E) contains the fixed non-MF group E
              (so neither LEF nor MF).                                 (TG2)
```

## Proof

*Upper bounds.*  MF is `Pi^0_2` for recursive presentations by
[[mf-recognition-recursive-presentations-is-second-level-complete]] (the
relator-prefix index is part of the scale), and LEF is `Pi^0_2` by
[[lef-recognition-has-a-pi2-upper-bound]].

*Hardness.*  Let `S_e` be the countably generated recursive presentation of
[[exact-literal-e-fin-inf-switch]], whose group is `1` for `e in INF` and the
literal forty-one-relator non-MF group `E` for `e in FIN`.  Enumerate its
generators as `c_1, c_2, ...` and put `c_i = 1` for `i <= 0`.  Let
`P_e = B2(S_e)` be the two-generator bidirectional bridge of
[[bidirectional-hnn-bridge-trivial-value-is-residually-finite]].  This is a
recursive presentation on the generators `a, t`, uniformly in `e`.

If `e in INF`, the switch group is trivial and `P_e ~= B2(1)`, which is
residually finite by the bridge claim; residually finite groups are LEF and
MF ([[mf-positive-controls]]).

If `e in FIN`, the switch group is `E`, and the HNN base `E * F(a,b)` embeds
in `B2(E)`.  Subgroups of MF groups are MF, and LEF groups are MF
([[lef-implies-operator-mf]]), so a group containing the non-MF group `E` is
neither MF nor LEF.

Thus `INF <=_m MF_rec2`, `INF <=_m LEF_rec2`, `FIN <=_m NONMF_rec2`, `FIN
<=_m NONLEF_rec2`, and `INF`, `FIN` are respectively `Pi^0_2`- and
`Sigma^0_2`-complete.

## Consequences for other properties

The same map separates every property `P` of finitely generated groups that
holds for `B2(1)` and fails for every group containing `E`.  Since `B2(1)` is
residually finite and `E` is not MF, this covers every subgroup-hereditary
`P` with

```text
residually finite  =>  P  =>  MF,
```

for example residual finiteness, residual amenability, MAP, LEF, MF, and
having MF full group C-star algebra.  For each such `P`, membership for
two-generator recursive presentations is `Pi^0_2`-hard.  Matching upper
bounds are established here for MF and LEF; residual finiteness of a
recursive presentation has only the obvious `Pi^0_3` upper bound (for every
word, either it is trivial or some assignment into a finite group kills every
relator and not the word), and closing that gap is left open.
