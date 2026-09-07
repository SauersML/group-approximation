---
rg: 2
id: binary-leavitt-unit-group-four-generated
kind: claim
title: Four explicit units generate the binary Leavitt unit group
artifacts:
  - experiments/atlas_four_generator_certificate.py
distinct_from:
  openai-leavitt-unit-nonsofic: that proves the unit group is nonsofic; this gives a short explicit generating set adapted to exact group-algebra searches.
  binary-leavitt-unit-group-is-minimally-almost-periodic: that is a representation-theoretic property of the same group, proved from property (T) of its elementary subgroups; this is a finite multiplication certificate naming two words per chart, and neither statement uses the other.
  leavitt-rank-three-unit-lift: that writes one nonunit as an additive sum of three units whose generated subgroup is virtually free; these four units generate the entire nonsofic group multiplicatively.
---

Let `Q=L_(F_2)(1,2)^x`, and let `K_1,K_2 ~= GL_4(F_2)` be the two
four-leaf chart groups in `notes/EXPLICIT_LEAVITT_ATLAS.md`.  Number the six
adjacent transvections in either chart by

```text
p_0=x_01, p_1=x_10, p_2=x_12, p_3=x_21, p_4=x_23, p_5=x_32.
```

In each chart put

```text
a=p_0 p_1 p_2,                    b=p_3 p_5 p_4.          (FG1)
```

Then the four units `a_1,b_1,a_2,b_2`, using `(FG1)` in the two charts,
generate `Q`.

Indeed exact enumeration in `GL_4(F_2)` shows

```text
|<p_0 p_1 p_2, p_3 p_5 p_4>| = 20160 = |GL_4(F_2)|.
```

Thus each pair generates its whole chart.  The two chart groups generate
`Q` by the Steinberg identities (7) in `notes/EXPLICIT_LEAVITT_ATLAS.md`, so
the four displayed units generate `Q`.

The computation is finite and exact: matrices are multiplied over `F_2` and
the generated subgroup is closed by breadth-first enumeration.  Run

```text
python experiments/atlas_four_generator_certificate.py
```

to reproduce the order `20160` certificate.

This is an upper bound of four on the multiplicative generator rank of `Q`,
not a proof that four is minimum.

