---
rg: 2
id: atlas-four-leg-coordinate-frame-extraction
kind: claim
title: Finite Atlas multiplicity selects a four-leg comb frame with one retained Pauli block
artifacts:
  - notes/ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md
  - notes/TRUE_RAW_PAULI_COEFFICIENT_CUT.md
  - notes/TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md
distinct_from:
  atlas-one-cut-finite-multiplicity-extraction: that states the terminal asymmetric cut directly; this names the smallest coordinate decoder and the exact four block identities which produce that cut.
  atlas-wedderburn-hall-deficient-support-certificate: that may aggregate many irreducible corners and a weighted min-cut; this asks for one four-leg frame and one retained upper block.
  pauli-block-tail-or-flat-rigidity-dichotomy: that splits according to singular values of the canonical sixteen-block Pauli table; this frame is necessarily noncanonical because the canonical table is Fourier-flat in every entry.
---

Let `delta` be the canonical regular-`A_8` atlas packet defect at external
multiplicity `k`.  In a fixed matrix amplification `N_k` of `M_k(C)`, select
four pairwise orthogonal equal-trace projections

```text
E_1,E_2,E_3,E_4,        E_1+E_2+E_3+E_4=1,
```

and a unitary `W in N_k`, obtained from the comb transport in one coherent
finite coefficient gauge, such that fixed constants `C,c>0` give

```text
sum_(j=1)^3 ||E_4 W E_j||_2^2 <= C delta^c,          (FCF1)
||E_1 W E_4||_2^2 >= 1/64-C delta^c.                (FCF2)
```

The value `1/64` is the ambient canonical mass of every raw-to-comb block in
`TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT`.  It is permissible to normalize on
the trace-half carrier instead, in which case the corresponding lower bound
is `1/32`; `(FCF2)` deliberately records the weaker ambient-normalized
constant.

The frame is the finite-coordinate shadow of the rank-four comb matrix

```text
[ s_0   0    0     p_1      ]
[  0   s_0   0     p_1 t_0  ]
[  0    0   s_0    p_1 t_0^2]
[  0    0    0     t_0^3    ].
```

Thus `(FCF1)` is the recovered lower-left algebraic zero row.  Condition
`(FCF2)` does not assert that the hidden coefficient `p_1` is itself an
ambient group polynomial.  It asks that one selected upper block be matched,
in the same gauge, to one of the already certified positive Pauli transition
blocks.

## Why this is the first missing identity

Three strictly weaker pieces are already available.

1. `TRUE_RAW_PAULI_COEFFICIENT_CUT` supplies an honest trace-half projection
   after removing a fixed Pauli factor.
2. `TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT` supplies the positive constant
   `1/64` without a rank or dilution argument.
3. The displayed comb matrix supplies the required triangular zero pattern
   in algebraic rank-four coordinates.

What is not known is one **common finite coefficient frame** in which the
second and third pieces refer to the same block of the same unitary.  This is
not cosmetic gauge fixing.  In the canonical four-character Pauli frame all
sixteen blocks have mass `1/64`, so the three blocks on the left of `(FCF1)`
have total mass `3/64`, not `o(1)`.  The selected `E_i` must therefore depend
on finite multiplicity/rank or singular-value data and cannot be the fixed
ambient Fourier cuts.

Nor can the `E_i` and `W` be obtained by one universal star-polynomial or
intrinsic finite-von-Neumann-algebra recipe.  The exact Leavitt factor model
satisfies the atlas relations and admits an internal relative-chart
conjugator.  Any such intrinsic recipe would give `(FCF1)--(FCF2)` in a
finite tracial algebra, contradicting unitary one-cut balance.  The selection
of this noncanonical finite frame is the theorem.

## Required proof shape

A viable proof must use finite external multiplicity before passing to the
tracial limit.  Equivalent formulations may use:

- a four-vertex coefficient quiver and a polar matching of equal-rank legs;
- a positive-density singular-value cut invariant under the relevant comb
  arrows; or
- a finite paired-radical quotient whose reduced Fourier transform identifies
  the algebraic zero row and the positive Pauli block.

Positive Hilbert--Schmidt mass alone is insufficient: polar truncation must
retain fixed mass and make the retained source and target dimensions match.
This is exactly the operator-level coordinate-extraction identity absent from
the five-row/collision data.
