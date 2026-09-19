---
rg: 2
id: literal-root-additivity-s4-leak-proof
kind: route
title: Verify the literal two-root denominator leak by cycle multiplication in S4
target: literal-root-additivity-rank-one-packet-has-s4-leak
requires: []
---

Put

```text
a=u=(2 3 4),       b=a^(-1)=(2 4 3),
h=(1 2)(3 4).
```

Then `u` commutes with both `a` and `b`. Since `a^3=1`, `b=a^(-1)`, and
`h^2=1`, the right side of `(RAS4-2)` reduces to

```text
a^2 (h a^2 h) a^2.                                     (S4P1)
```

Conjugating the middle cycle gives

```text
h a^2 h=(1 3 4).
```

With products composed from right to left, direct multiplication gives

```text
(2 4 3)(1 3 4)(2 4 3)=(1 2)(3 4)=h,                  (S4P2)
```

so `(RAS4-2)` holds. On the other hand, `a` and `h` do not commute: for
example

```text
a h(1)=3,             h a(1)=2.
```

Hence `[u,h]` is nonidentity. The normalized character of the left regular
representation of a finite group is one at the identity and zero elsewhere,
so its value at `[u,h]` is zero. This proves all assertions of the target.
