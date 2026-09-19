---
rg: 2
id: expander-edge-simplex-wedge-proof
kind: route
title: Apply expander mixing to the balanced affine-label fibers
target: expander-edge-overlay-detects-simplex-exterior-square
requires: []
---

For every sufficiently large power of two, choose a constant-degree regular
graph whose normalized adjacency operator has absolute nontrivial spectrum at
most `lambda=1/8`.  The standard random-regular-graph probabilistic
construction gives such graphs after fixing one sufficiently large degree.
For the finitely many smaller powers of two choose the complete graph and
increase the universal degree bound if necessary; `(SEO3)` is then checked
directly (a complete graph samples every distinct pair, which is at least as
strong as the estimates below).

Write `F=(u,v):A->F_2^2`.  If `u,v` are dependent, all values of `F` lie in
one linear line, so every determinant in `(SEO2)` is zero.  Suppose they are
independent.  There are two cases.

If the linear part of `F` has rank one, its image is an affine line not
through zero.  Its two values `p,q` are linearly independent and each fiber
has density `1/2`.  Thus `D=1/2`.  If `s` is the balanced sign distinguishing
the two fibers, the spectral bound gives

```text
L_G = Pr_(x~y)[s(x) != s(y)]
    = (1-<s,Ps>)/2 >= (1-lambda)/2 = 7/16.                 (SEP1)
```

If the linear part has rank two, all four fibers `A_p=F^{-1}(p)` have density
`1/4`, and `D=6/16=3/8`.  For two distinct nonzero labels `p,q`, expander
mixing in normalized counting measure gives

```text
Pr_(x~y)[x in A_p, y in A_q]
 >= 1/16-lambda*sqrt((1/4)(3/4)(1/4)(3/4))
 = (1-3 lambda)/16.                                       (SEP2)
```

There are six ordered pairs with `det(p,q)=1`.  Hence

```text
L_G >= 6(1-3 lambda)/16 = 15/64.                           (SEP3)
```

Equations `(SEP1)--(SEP3)` imply `D/L_G<=8/7` in the rank-one
case and `D/L_G<=8/5` in the rank-two case, proving `(SEO3)`.

On an edge `{x,y}`, the two restricted section rows have rank two exactly
when `det(p_x,p_y)=1`.  Therefore `(SEO3)` is precisely robust injectivity on
decomposable exterior squares.  Giving an edge one joint binary PVM tests
commutation of its two coordinate reflections but accepts every classical
pair of bits, so the overlay changes neither the classical kernel nor the
local alphabet size.  Simplicity of `G_n` ensures distinct views have no
two-coordinate overlap.
