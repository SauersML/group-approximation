---
rg: 2
id: extended-asymmetric-prefix-relative-source-proof
kind: route
title: Compare the extended prefix cycle with J1J2 on the complete signed source
target: extended-prefix-relative-word-centralizes-quarter-source
requires:
  - asymmetric-prefix-unit-conjugates-native-whiteheads
  - b2-b3-pair-full-hecke-four-native-sectors
  - native-whitehead-corner-collapses-hecke-flags
---

The three nontrivial diagonal entries of `D~` on the native coordinates are

```text
d_7=u,                  d_8=u,                  d_9=u^(-2).
```

Prefix cancellation in the two complete codes defining `u` gives

```text
u b_2=b_3,                 u^(-2)b_3=b_1,
u^(-2)(b_3a_1)u^(-1)=y_1,                              (1)
a_1u^(-1)=a_2,             a_2u^(-1)=a_3,
a_3u^2=a_1.                                             (2)
```

Here `y_1=s_0t_00`.  Conjugation by a diagonal elementary torus sends
`x_ij(a)` to `x_ij(d_i a d_j^(-1))`, and `P` then applies the coordinate
cycle.  Equations `(1)--(2)` therefore give the following complete table:

```text
generator   C3  C2  C1   d    f          k          c          v  w  s  r  l
G~-image    C3  C2  C1   k   x_74(b_1)  x_72(b_1)  x_78(y_1)  r  s  l  t  w,
                                                               (3)
```

where `t=x_59(a_3)`.  The same calculation also gives `G~tG~^(-1)=v`, so
the two native triples are cycled as

```text
(v r t),                         (w s l).              (4)
```

Now expand the two partial Whitehead blocks

```text
J_1=x_87(x_1)x_78(y_1)x_87(x_1),
J_2=x_98(x_2)x_89(y_2)x_98(x_2).
```

Ordinary block multiplication, using `y_ix_i=e_(0^i)` and
`x_iy_i=e_(0^(i+1))`, gives for `A=J_1J_2` exactly the same row `(3)`.
In particular it gives `(4)`, while on the remaining four noncentral
generators it gives

```text
d |-> k,
f |-> x_74(b_1),
k |-> x_72(b_1),
c |-> x_78(y_1).                                     (5)
```

All three center roots are fixed.  These are ordinary non-opposite
Steinberg calculations, so the displayed conjugation identities hold for
the root words themselves, not merely after taking a matrix trace.

For each generator `x` in `(3)`, equality of the two images implies

```text
R x R^(-1)
 =A^(-1)(G~xG~^(-1))A
 =x.                                                   (6)
```

This proves the first three commutators in `(EAR4)`.  Both `G~` and `A`
conjugate `J_1` to `J_2`: for `G~` this is the same prefix calculation as
for the shorter diagonal, since the new coordinate-`9` torus is disjoint
from `J_1`; for `A` it is the Coxeter braid.  Hence

```text
RJ_1R^(-1)=A^(-1)J_2A=J_1,                            (7)
```

which completes `(EAR4)`.  Since `Q` is the signed average of `L_0`, (6)
fixes `Q`; fixing `r,l` then fixes `F`, proving `(EAR5)`.

Finally the canonical elementary image of `A` is the identity on spare
coordinates `10,11,12`, while `G~` has respective diagonal entries
`u^(-1),u^(-1),u^2` there.  Hence `R` retains those entries.  The identity
`us_0=s_00` proves `u!=1`, so `R!=1`.  This proves that the relative factor
is a nontrivial fixed-source gauge rather than a cancellation.

`experiments/asymmetric_prefix_relative_source_audit.py` independently
replays `(1)--(7)` in faithful binary-prefix normal form.  Its MSI output
reports equality of the `G~` and `J_1J_2` images, and fixedness under `R`,
for all twelve generators with no failures.
