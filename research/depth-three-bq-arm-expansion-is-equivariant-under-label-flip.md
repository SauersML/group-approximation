---
rg: 2
id: depth-three-bq-arm-expansion-is-equivariant-under-label-flip
kind: claim
title: The canonical depth-three Bleak--Quick arm expansion is equivariant under the label flip
invalidates:
  - natural-depth-three-r2-r3-expansion-exposes-shared-endpoint
distinct_from:
  common-pivot-r2-r3-data-preserve-a6-label-swap: that gives abstract six- and twelve-point permutation countermodels; this expands the actual depth-three swap words defined by Bleak and Quick and locates the surviving gauge inside those words.
  shared-endpoint-r2-r3-anchor-has-linear-seam-bound: that proves synchronization once an endpoint or complementary child is literally common; this proves the canonical address expansion supplies no such label-sensitive common datum.
  finite-mark-centralizer-commutator-area-is-proper: that is an unbounded-area theorem for escaping endpoint corrections; this is a fixed depth-three syntactic obstruction before any long address transport occurs.
---

Use the six depth-three cylinders

```text
p=000, q=001, i=010, j=011, k=100, l=101
```

and write `tau_(alpha,beta)` for the exact Bleak--Quick word denoted
`(alpha beta)`.  Put

```text
r=tau_(000,001),                 f=tau_(010,011),
s_i=tau_(010,000),               t_i=tau_(010,001),
s_j=tau_(011,000),               t_j=tau_(011,001),
c_i=s_i t_i,                     c_j=s_j t_j.                   (DTE1)
```

These are literal words from Definitions D:33 and D:other33 of the
Bleak--Quick presentation.  More explicitly,

```text
r   = tau_(1,000)^tau_(1,001),
s_i = tau_(1,000)^tau_(1,010),
s_j = tau_(000,011),
t_i = tau_(000,011)^a,
t_j = tau_(001,011),
f   = r^a,                         a=tau_(00,01),                 (DTE2)
```

where the formula for `t_i` uses D:other33 with
`rho_(01,00)=a`, and the last formula is the D:33 definition
`tau_(xy0,xy1)=tau_(000,001)^tau_(00,xy)` at `xy=01`.
The order in `c_i=s_i t_i` follows Bleak--Quick's right-action convention,
under which `b=tau_(01,10)tau_(01,11)` induces `(01 10 11)`.

The canonical R2 arm triangles are

```text
s_i^r=t_i,                       s_j^r=t_j.                       (DTE3)
```

But the label flip transports the entire first triangle to the second:

```text
f^(-1) r f=r,       s_i^f=s_j,       t_i^f=t_j,       c_i^f=c_j. (DTE4)
```

Thus `r` is the only common endpoint.  Neither the R2 input nor its output
is retained across the two contextual occurrences.

The same failure persists after the literal R3 refinements

```text
s_i=tau_(0100,0000) tau_(0101,0001),
t_i=tau_(0100,0010) tau_(0101,0011),                            (DTE5)
```

because conjugation by `f` replaces every prefix `010 epsilon` by
`011 epsilon` and carries both children to the corresponding children of
`s_j,t_j`.  Splitting the pivot `r` gives common children, but they are
permutation-invariant pivot data and contain no occurrence of the label.

Finally, the contextual Carmichael cycles really are conjugates of the
marked generator.  Let `g in V` be the prefix replacement from the maximal
source code

```text
{000,001,01,10,11}
```

to the maximal target code

```text
{011,1,010,000,001}
```

which sends `01,10,11` respectively to `010,000,001` and sends the two
fixed source leaves `000,001` to `011,1`.  Then

```text
b^g=c_i,                         b^(g f)=c_j.                     (DTE6)
```

Consequently the canonical adjacent-chart shared-label words are precisely
`b^g` and `b^(gf)`: their discrepancy is the explicit depth-three label
flip `f`.  One canonical R2 triangle, one canonical R3 refinement, or any
combination obtained by applying the same refinement equivariantly to both
contexts cannot produce the shared endpoint required by `(BQA2)` or
`(BQA3)`.  A surviving proof must use an additional asymmetric cell or an
interacting multi-cell diagram which prevents `f` from transporting the
whole address packet.
