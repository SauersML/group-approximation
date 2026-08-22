---
rg: 2
id: macroscopic-zero-compression-universality-proof
kind: route
title: Compress a finite regular representation to a Cayley independent set
target: macroscopic-zero-compressions-make-polar-data-universal
requires: []
---

Residual finiteness gives a finite quotient `q:G->Q` in which every element
of `S` remains nonidentity.  Form the loop-free undirected Cayley graph of
`Q` for `q(S)`.  A greedy algorithm supplies a nonempty independent set
`B`; quantitatively one may take

```text
|B| >= |Q|/(|S|+1).                                      (MZC4)
```

Let `lambda_Q` be the left regular representation.  Independence says

```text
P_B lambda_Q(q(s)) P_B=0                 (s in S),       (MZC5)
```

where `P_B` projects onto `ell^2(B)`.

Amplify `lambda_Q` by an identity multiplicity large enough that
`ell^2(B)` tensored with the multiplicity space has dimension at least `d`.
Choose any rank-`d` subprojection `P` inside that space.  Equation `(MZC5)`
still gives `(MZC2)`.  Since `pi(s)` is unitary and its image of `PH` is
orthogonal to `PH`, `(1-P)pi(s)P=pi(s)P` has Hilbert--Schmidt square `d`,
which proves `(MZC3)`.

The zero operator has polar decomposition `0=W|0|` for every unitary `W`:
the partial polar isometry has zero initial space, so its unitary extension
is arbitrary.  Taking that extension to be the prescribed `U_s` realizes
all of `(MZC1)` as polar-correction data of the one exact representation
`pi` and the common projection `P`.

