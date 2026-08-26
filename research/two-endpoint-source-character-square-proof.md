---
rg: 2
id: two-endpoint-source-character-square-proof
kind: route
title: Compute the joint endpoint annihilator and build its four-character source model
target: two-endpoint-source-intersections-retain-character-square
requires:
  - endpoint-whitehead-signed-source-has-only-relative-hecke-overlap
  - endpoint-detector-cell-retains-coboundary-gauge
---

Use the faithful `8192`-element binary matrix table of `L_0`.  A single
breadth-first traversal records, for every group element, the parity vector
of one word in the ten displayed generators.  Every alternate word gives a
linear relation among those ten parities.  The orthogonal complement of the
relation span is the full character group and has `256` elements.

Impose the exact row-and-column conditions from
`endpoint-whitehead-signed-source-intersection-proof`.  They give

```text
|K_2|=256,             |K_4|=512,             |K_2 cap K_4|=32.       (1)
```

Testing the `256` character masks on these subgroups gives

```text
Ann(K_2)={0,4,8,12},
Ann(K_4)={0,2,4,6,16,18,20,22},
Ann(<K_2,K_4>)={0,4}.                                  (2)
```

Here bit `4` is `xi_2` and bit `2` is `xi_4`.  Equations `(1)--(2)` prove
`(TES1)--(TES2)`.  Direct evaluation on the three representatives

```text
(65,74,4,8,16,32,64),
(73, 2,4,8,16,32,64),
(73,74,4,8,16,32,64)
```

gives zero for `lambda_0`, `xi_2`, and `xi_4` in additive sign notation,
which is `(TES5)`.  The deterministic MSI audit
`experiments/endpoint_two_source_character_audit.py` performs exactly these
finite calculations.

For the operator fence, index four orthogonal lines by `(a,b) in F_2^2` and
represent `g in L_0` on the `(a,b)` line by

```text
lambda_0(g) xi_2(g)^a xi_4(g)^b.
```

Let the two endpoint words flip the first and second bit respectively.
Because the applicable twist is trivial on the corresponding `K_r`, each
flip commutes with the full represented intersection subgroup and realizes
the endpoint amalgam table exactly.  The four Reynolds projections are the
four coordinate lines, proving `(TES4)`.

Finally take four character twists of any exact finite endpoint-occurrence
block.  Character scalars cancel from group commutators, and `(TES5)` shows
that the three named detector representatives themselves have identical
sign on all four source charts.  Define every external probe, endpoint leg
and returned root blockwise, and let the two flips transport those blocks.
Thus the nested detector and mark-return equations are copied exactly to
all four charts while the source projections remain orthogonal.  This is
the claimed scoped countermodel.
