---
rg: 2
id: affine-simplex-riesz-inverse-is-uniformly-cb
kind: claim
title: The affine-simplex coordinate Riesz inverse is uniformly completely bounded
distinct_from:
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that isolates a possible unbounded code-dependent Schur multiplier; this proves a uniform bound for the two-weight affine simplex code.
  code-riesz-inverse-is-averaged-first-split: that represents arbitrary support averages by random filtrations and leaves an endpoint loss; this uses the exact two-weight spectrum to avoid martingale truncation.
  expander-edge-overlay-detects-simplex-exterior-square: that detects scalar exterior-square directions with bounded incidence; this is an operator row-column estimate at an exact global simplex representation.
---

ESTABLISHED.  Let `A=F_2^n`, `L=|A|`, and let

```text
C={x |-> a.x+c : a in F_2^n, c in F_2} <=F_2^A          (ASR1)
```

be the full affine simplex code.  In an exact representation of its abelian
code group, decompose by code characters.  For a character difference
`z in C`, write `S=supp(z)`.  The transverse complete-pair inverse is

```text
T_i(b)(z)=(1/|S|) sum_(j in S) b_(i,j)(z).                (ASR2)
```

With the input normalized over `(i,j)` and the output normalized over `i`,
`T` has completely bounded operator column and row norm at most `3`,
uniformly in `n`, matrix dimension, and character multiplicities.

Indeed every nonzero affine word other than the constant-one word `z_0`
has weight `L/2`, while `wt(z_0)=L`.  Hence

```text
1_(z_j=1)/|S|
 = (2/L)1_(z_j=1)-(1/L)1_(z=z_0).                        (ASR3)
```

Both Schur masks are complete contractions.  The first is
`(I-Ad(Q_j))/2`; the second selects the disjoint character-block matching
`chi <-> chi+z_0`.  Column Cauchy--Schwarz, followed by the normalizations,
gives cb norm at most `2` for the first term and at most `1` for the second.
The adjoint calculation gives the row estimate.

Thus the exact-base Riesz/BMO obstruction in the balanced LDPC lane is not
intrinsic to growing Pauli rank: an equidistant/two-weight code removes it
algebraically.  This does not yet prove an affine-simplex operator decoder.
One still needs a bounded-occurrence presentation with uniform off-exact
agreement/basin capture; `bounded-template-average-blr-occurrence-decoder`
is precisely that separate global problem.

