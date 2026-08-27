---
rg: 2
id: kl-packet-inner-breaks-prefix-tree-induction-proof
kind: route
title: Compute the nonzero off-diagonal commutator of the two primitive support idempotents
target: kl-packet-inner-breaks-prefix-tree-induction
requires:
  - degree-four-kl-inner-retractions-fail
---

In the binary Leavitt algebra put

```text
e0=s0 t0,       e1=s1 t1,       e0+e1=1,
E0=e0 I_20,     E1=e1 I_20.                              (PI1)
```

These are the support idempotents of the two primitive corner embeddings.
Take `X=x_34(s1)=I+s1 E_34`.  In characteristic two `X^(-1)=X`, and
`E_34^2=0`, so direct multiplication gives

```text
X E0 X^(-1)=E0+f E_34,
f=s1 e0+e0 s1=s1 s0 t0.                                (PI2)
```

Here `e0 s1=s0(t0s1)=0`.  The remaining coefficient is nonzero: if
`f=0`, left multiplication by `t1` would give
`0=t1f=s0t0=e0`, whereas `t0 e0 s0=1`.

Now compare the two products with `E1`.  Their `(3,4)` entries are

```text
f e1=s1 s0 (t0s1)t1=0,
e1 f=s1(t1s1)s0t0=f != 0.                              (PI3)
```

Thus `X E0 X^(-1)` and `E1` do not commute.  The second factor
`x_(11,12)(t0)` of `q` has disjoint matrix support.  Its conjugation changes
only the `(11,12)` entry and cannot cancel the nonzero `(3,4)` discrepancy in
`(PI3)`.  Therefore

```text
[q E0 q^(-1), E1] != 0.                                (PI4)
```

So the images of `Ad(q) o iota_0` and `iota_1` are not blocks of a common
prefix decomposition.  This is already the two-leaf tree, hence no induction
on larger prefix codes can start once packet-inner conjugators are allowed.

## Why the first noncommutative incidence invariant also fails

For ordered support idempotents, record only whether `P_iP_j` is zero.  Before
conjugation, `(PI1)` gives

```text
E0 E1=E1 E0=0.                                         (PI5)
```

After conjugating the first support by `X`, equations `(PI2)--(PI3)` sharpen
to

```text
(X E0 X^(-1)) E1=0,
E1 (X E0 X^(-1))=f E_34 != 0.                          (PI6)
```

Thus one allowed packet-inner operation changes the directed incidence type
from `(0,0)` to `(0,1)`.  Because the three coefficient-copy embeddings may
be composed independently, simultaneous-conjugacy invariance does not rescue
this Boolean matrix.

Literal leading terms in Bergman path-pair normal form do not give a fixed
finite substitute.  Applying a depth-`n` corner replaces every active
coefficient `r` by `s_v r t_v`, `|v|=n`; hence both path lengths move beyond
any prescribed bounded window.  The corner map is injective, so this is not
vanishing information--it is information escaping to arbitrary scale.  A
successful invariant would have to strip or compare prefixes coherently at
all depths, while `(PI6)` shows that packet-inner conjugation destroys the
common prefix decomposition needed to perform that stripping.

There is a second obstruction in the actual orbit relator.  Its zeroth copy
is fixed rather than corner-supported, and its coefficients include `s0`,
`t1`, and the mixed `q`; the pivot `z` solved from `R0` inherits those prefix
changes.  Accordingly, orthogonality of the three *other* copy supports would
still not make `R1` block diagonal.  The exact finite screens remain valid,
but a tree induction requires additional control not present in prefix
support alone.
