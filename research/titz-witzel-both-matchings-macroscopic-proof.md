---
rg: 2
id: titz-witzel-both-matchings-macroscopic-proof
kind: route
title: Collapse the second coupling word when the first matching is trivial
target: titz-witzel-both-matchings-need-macroscopic-support
requires:
  - titz-witzel-sofic-gate-has-only-seven-relators
  - titz-witzel-trivial-second-matching-collapses-mark
---

The case `d_H(e_n,1)->0` is the asymptotic conclusion of
`titz-witzel-trivial-second-matching-collapses-mark`.

Suppose instead that `d_H(c_n,1)->0`.  Replace `c_n` by the identity.  The
word `Y=r^2e^(-1)` is independent of `c`, so this does not change the marked
permutation at all.  Since every defining word has fixed length, normalized
Hamming bi-invariance shows that all five coupling defects remain `o(1)`.
It is therefore enough to analyze `c=1` exactly.

When `c=1`, the definitions `(TW8)` give `X=Y^(-2)`.  The second coupling
word freely reduces as follows:

```text
X r c S
 =Y^(-2) r r^(-1) X^(-1)Y r^(-2)
 =Y^(-2)Y^2Y r^(-2)
 =Y r^(-2)
 =H^(-1).                                                       (1)
```

Here `H=r^2Y^(-1)=YeY^(-1)`, because `Y=r^2e^(-1)` and `e^2=1`.
Consequently

```text
d_H(XrcS,1)=d_H(H,1)=d_H(e,1).                               (2)
```

Small defect of the second coupling equation thus forces
`d_H(e_n,1)->0`.  The second-matching collapse theorem then implies
`d_H(Y_n^8,1)->0`, contradicting the marked objective.  This proves both
alternatives in `(TBM1)`.

For the explicit bound, write `alpha=d_H(c,1)`.  Replace `c` by the identity
and use primes for the resulting words.  Expanded in the base variables,
the second coupling word contains three occurrences of `c^+-1`, the third
contains four, and the fourth contains three.  Hence

```text
delta_2' <= delta_2+3alpha,
delta_3' <= delta_3+4alpha,
delta_4' <= delta_4+3alpha.                               (3)
```

The marked word is unchanged because `Y` is independent of `c`.  Equations
(1)--(2) give `d_H(e,1)=delta_2'` for the primed triple.  Apply `(TEM3)` to
that triple and then (3):

```text
d_H(Y^8,1)
 <=8delta_3'+16delta_4'+296delta_2'
 <=296delta_2+8delta_3+16delta_4+968alpha.
```

This is `(TBM2)`.  Its support bounds and the corresponding bound
`(TEM3)` for `e` follow by taking the liminf along a marked subsequence.
