---
rg: 2
id: character-carrier-wandering-floor-proof
kind: route
title: Split between character-Hecke leakage and a stabilized square-return floor
target: character-carrier-wandering-floor
requires: []
---

Write `A=q w q`, `K'=w^(-1)Kw`, and `q'=w^(-1)qw`.  Direct expansion of
the two character sums gives

```text
||A||_2^2=tau(q'q)
 = |K cap K'|/|K|^2                                   (FCF2)
```

when the two transported characters agree on `K cap K'`, and gives zero
otherwise.  Since `||V||_2=sqrt(beta)`, the reverse triangle inequality
gives

```text
||A-V||_2 >= sqrt(beta)-||A||_2.                       (FCF3)
```

Unless conjugation by `w` preserves both `K` and `chi`, either the
intersection is a proper subgroup of `K`, of size at most `|K|/2`, or the
character sum vanishes.  Equations `(FCF2)--(FCF3)` then give `(FCF1)`.

In the remaining case `q'=q`, so `w` commutes with `q` and `A=qw` is a
unitary in the corner.  Since `V^2=q`, telescoping the square gives

```text
||(w^2-1)q||_2=||A^2-V^2||_2
 <= 2||A-V||_2.                                       (FCF4)
```

Infinite order of `w` implies `w^2 notin K`: conjugation normalizes `K`,
and if `w^2` belonged to finite `K`, then a positive even power of `w`
would be one.  Hence the supports `K` and `K w^2` are disjoint and

```text
||(w^2-1)q||_2=sqrt(2 beta).
```

This branch gives the stronger bound `1/sqrt(2|K|)`, completing `(FCF1)`.
All quantities used above are moments of one fixed finite set of group
words.  Canonical-profile convergence therefore transfers the bound to
matrix tuples with an `o(1)` loss; fixed finite-packet exactification also
changes it by only `o(1)`.
