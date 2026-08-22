---
rg: 2
id: leavitt-d4-l14-n0511-five-branches-share-one-core
kind: claim
title: All five normal six-winner branches share one two-copy carrier and one eighteen-syllable boundary
distinct_from:
  leavitt-d4-l14-n0511-branch-i-needs-nontrivial-carrier: that fences the trivial-carrier stratum of branch I; this proves that branches II through V reduce to the identical carrier and boundary and isolates every remaining identity stratum.
  leavitt-d4-l14-seven-syllable-splitter: that classifies the five abstract noncrossing partitions; this substitutes each partition into the fresh normal 0;511 carrier equations.
  leavitt-d4-l14-rank9-n0115-is-fenced: that fully fences a class in the first profile by unique-copy syllables; this exposes the different periodic eighteen-syllable core left by the second profile.
---

# All five normal six-winner branches share one two-copy carrier and one eighteen-syllable boundary

**ESTABLISHED.**  Retain notation `(N51-1)--(N51-2)`.  After `r=1` and
`A0=1`, the five maximal branches are

```text
I:   q=e=g=1,       a d f t=1;
II:  q=f=1,         e g=1,       a d t=1;
III: d=g=1,         q e=1,       a f t=1;
IV:  d=f=1,         q e g=1,     a t=1;
V:   e=1,           q g=1, d f=1, a t=1.               (N5C1)
```

In every branch the remaining carrier equations reduce to

```text
H=k_1 a^-1_2,
k b=t a,
m:=b^-1=a^-1t^-1k,
l=a^-1.                                                   (N5C2)
```

More precisely, the copy-zero part of `B1` is always `m`, while its
copy-one part is always `a^-1`; the apparently different products in
branches III--V collapse using `q=bc` and `(N5C1)`.

Consequently all five branches have exactly the same coefficient boundary:

```text
F=
a_2 k^-1_1 i_0 j_1 k_2 a^-1_3
a_2 k^-1_1 m_0 a^-1_1 i_2 j_3
a_2 k^-1_1 t_0 i_1 j_2 k_3.                            (N5C3)
```

Its copy pattern is the periodic word

```text
(2,1,0,1,2,3)^3.                                       (N5C4)
```

Thus if all six coefficient syllables

```text
a, k, i, j, t, m=a^-1t^-1k                            (N5C5)
```

are nonidentity, `(N5C3)` is reduced of length eighteen and cannot be a
one-copy word.  If `H=1`, the preceding branch-I theorem applies verbatim
because `(N5C3)` is now branch-independent and fences that stratum as well.

Every surviving normal `0;511` carrier must therefore satisfy both

```text
k_1a^-1_2 !=1
```

and at least one of the six identity conditions in `(N5C5)`.  The new
profile does not leave five unrelated nonlinear searches: it leaves one
explicit two-copy core and a finite union of identity strata.  Whether any
of those nontrivial-carrier strata reduces to a one-copy boundary remains
open.

