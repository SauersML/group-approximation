---
rg: 2
id: two-cone-central-router-determinant
kind: claim
title: A coprime two-cone central router reduces to one determinant
distinct_from:
  central-word-state-face-compiler: that asks for a nonlinear whole-state-face compiler; this is only the exact abelian arithmetic of a three-generator central presentation.
  source-specific-pointed-rank-router-face: that asks for finite-matrix rank routing on a selected source face; this is an exact Smith-normal-form gadget with no approximation statement.
artifacts:
  - research/artifacts/seifert-coinvariant-router-2026-08-23.md
---

Let `m,n >= 2` be coprime and let `e,a,b` be integers.  Define

```text
R(m,n;e,a,b) =
<c,x,y | c central, x y = c^e, x^m = c^a, y^n = c^b>.
```

Then `R(m,n;e,a,b)` is abelian.  Put

```text
D = m n e - n a - m b.
```

If `D != 0`, then

```text
R(m,n;e,a,b) ~= Z/|D|Z.
```

If `D = 0`, then `R(m,n;e,a,b) ~= Z`.

Equivalently, after eliminating `y`, the whole router is the cokernel of the
integer relation matrix

```text
[ m   -a     ]
[ n   b-ne   ],
```

whose first Smith divisor is one because `gcd(m,n)=1` and whose determinant
is `-D`.
