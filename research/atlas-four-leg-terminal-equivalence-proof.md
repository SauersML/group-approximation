---
rg: 2
id: atlas-four-leg-terminal-equivalence-proof
kind: route
title: Compare the retained four-leg block with the whole forbidden row
target: atlas-four-leg-frame-is-terminal-defect-gap
requires:
  - finite-tracial-one-cut-balance
---

Let `E_1,...,E_4` be pairwise orthogonal projections summing to one, let `W`
be unitary, and put

```text
P=E_1+E_2+E_3,
L=sum_(j=1)^3 ||E_4 W E_j||_2^2,
R=||E_1 W E_4||_2^2.
```

Orthogonality and one-cut balance give

```text
L = ||(1-P) W P||_2^2
  = ||P W (1-P)||_2^2
  = sum_(i=1)^3 ||E_i W E_4||_2^2
  >= R.                                                (FTE3)
```

Consequently `(FCF1)--(FCF2)` imply

```text
1/64-C delta^c <= R <= L <= C delta^c.
```

This is `1/64<=2C delta^c`, proving `(FTE1)`.  Notice that neither equal
trace nor any coordinate origin of the projections is used in this
direction.

For the converse, suppose `delta>=epsilon>0`.  Pass to the fixed fourfold
amplification and take its four standard equal-trace coordinate projections.
For any unitary `W`,

```text
L=||E_4 W P||_2^2 <= ||E_4 W||_2^2=tau(E_4)=1/4,
R>=0.                                                  (FTE4)
```

With `C` as in `(FTE2)`, one has `C delta^c>=1/4`.
Equation `(FTE4)` proves `(FCF1)`, while

```text
1/64-C delta^c <= 1/64-1/4 < 0 <= R
```

proves `(FCF2)`.  The argument applies in particular to any available
coefficient comb unitary.  This establishes the claimed equivalence.
