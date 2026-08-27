---
rg: 2
id: binary-leavitt-canonical-morita-tree-proof
kind: route
title: Strip the common branch prefix and leave one contextual zero relation
target: binary-leavitt-canonical-morita-tree-reduction
requires:
  - stabilized-morita-branches-are-inner-but-incoherent
  - infinite-chromatic-commutator-code-kills-mf-mark
---

For any words `g,x,y`, the commutator of two simultaneous conjugates is
freely the same simultaneous conjugate:

```text
[gxg^(-1),gyg^(-1)]=g[x,y]g^(-1).                       (1)
```

Apply `(1)` with `g=D_u` to the two base words in `(MTR1)`.  This proves
`(MTR3)` with the fixed area of `[c,h]z^(-1)`; the length of `D_u` is not
charged because it is only a conjugating word.

Now take distinct words at one depth and split off their longest common
prefix as in `(MTR5)`.  The recursion `D_(pu)=D_pD_u` and `(1)` give, by free
reduction,

```text
[c_(pia),h_(pjb)]
 =D_p[c_(ia),h_(jb)]D_p^(-1).                            (2)
```

The two tails in `(2)` have the same length because the original vertices do.
Hence the assumed level-synchronous first-mismatch bound `(MTR4)` pays every
off-diagonal cell with the same number of defining relators.

Finally `(SMI2)` says that the outer branch `D_i` multiplies an `X`-root
coefficient on the right by `t_i`, while `D_j` multiplies a `Y`-root
coefficient on the left by `s_j`.  Their Steinberg commutator coefficient is
therefore

```text
r_a(t_i s_j)s_b=0                                        (3)
```

when `i!=j`.  This proves the exact statement `(MTR6)` and shows why tails
are contexts, not additional mismatches.  Complete depth-`n` vertex sets and
`(MTR3)--(MTR4)` satisfy `(CCC1)--(CCC2)`, proving the reduction.
