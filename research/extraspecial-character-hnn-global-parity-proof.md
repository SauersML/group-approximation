---
rg: 2
id: extraspecial-character-hnn-global-parity-proof
kind: route
title: Compare the source and transported characters on their HNN intersection
target: extraspecial-character-hnn-two-cycle-forces-global-parity
requires:
  - finite-cocycle-select-forces-one-common-lcu-gauge
  - extraspecial-common-gauge-fourier-controller
  - stabilizer-corrector-hermitianizes-zero-compression
  - central-marked-two-cycle-zero-compression-cell
---

For a finite subgroup `H`, character `chi`, character idempotent `q_chi`,
and group element `v`, direct expansion of the two character sums shows

```text
q_chi v q_chi=0
```

exactly when `chi` and its `v`-transport disagree on
`H intersect vHv^(-1)`. If they agree, the same expansion has positive
squared regular norm

```text
|H intersect vHv^(-1)|/|H|^2.
```

Apply this with `(ECH1)--(ECH3)` and `v=V`. Every equality witnessing an
intersection element has the form

```text
J^epsilon X_b
 =V(J^eta X_a)V
 =J^eta U_a X_a.                                      (ECH6)
```

The source character and transported character take the values
`(-1)^epsilon` and `(-1)^eta`. They disagree exactly when
`epsilon+eta=1`. Rearranging `(ECH6)` then gives

```text
U_a=J X_(a+b).
```

Conversely any such equality supplies an intersection element on which the
characters disagree, proving `(ECH4)`.

In a tensor-spin completion, `U_a` is identity on the irreducible Pauli
factor, while `JX_c` is `-X_c` there. If `c` is nonzero, `X_c` is a
non-scalar Pauli operator, so equality is impossible. Hence `c=0` and the
relation is exactly `U_a=-1`. Embedding of `H` excludes `a=0`.

For the countermodel, diagonalize the payload over every nonzero
`chi in K^dual`. The Reynolds average `P_K` is the projection onto the
trivial character and is therefore zero. The exact controller formula with
`A=1` gives an involution `C`, so `S=1` is already a valid corrector. For
each nonzero `a`, because `k>1`, the hyperplane `a^perp` contains a nonzero
`chi`; on that eigenspace `U_a=1`. Thus no `U_a` is globally `-1`.

Finally, canonical regular trace gives `tau(q)=1/|H|=2^(-(k+1))`. The
two-grading cell gives trace `1/4` when its three grading words are
nonidentity. These differ for `k>1`, proving the literal-source mismatch and
completing the composition obstruction.
