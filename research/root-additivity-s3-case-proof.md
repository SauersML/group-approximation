---
rg: 2
id: root-additivity-s3-case-proof
kind: route
title: Split according to the three possible centralizers in S3
target: root-additivity-eliminates-the-s3-rank-one-leak
requires: []
---

There are three cases.

If `u=1`, `(RAS3)` is immediate.

If `u` is a transposition, its centralizer is `{1,u}`. Hence `(RAS1)` puts
`a,b` in `{1,u}`. Their squares are both one, so `(RAS2)` reduces to

```text
h=a b a^(-1)=b,
```

where the last equality uses commutativity of the two-element centralizer.
Thus `h` centralizes `u`.

Finally suppose `u` is a three-cycle. Its centralizer is the normal cyclic
subgroup `A_3`, so `a,b in A_3`. If `h in A_3`, we are done. Otherwise `h`
is a transposition and conjugation by `h` inverts every element of `A_3`.
Since `a` and `b` commute and `b^3=1`, the right side of `(RAS2)` becomes

```text
a^2 (b^(-2))^(-1) a b a^(-1)
 =a^2 b^2 b
 =a^2 in A_3.                                            (RAP1)
```

It cannot equal the transposition `h`. This contradiction rules out the
only noncentral case, completing the proof.

