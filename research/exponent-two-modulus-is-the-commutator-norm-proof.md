---
rg: 2
id: exponent-two-modulus-is-the-commutator-norm-proof
kind: route
title: Expand the square and use unitary invariance of the norm
target: exponent-two-modulus-is-the-commutator-norm
requires: []
---

With `U^2 = V^2 = I`,

```text
U (VU - UV) V = (UV)(UV) - (UU)(VV) = (UV)^2 - I,
```

using associativity only. Since `U` and `V` are unitary, left and right
multiplication by them are isometries of the operator norm, so

```text
|| (UV)^2 - I || = || U (VU - UV) V || = || VU - UV || = || UV - VU ||,
```

which is `(E2M1)`.

**Approximate form.** Suppose only `||U^2 - I|| <= a` and `||V^2 - I|| <= b`
for unitaries `U, V`. Then

```text
(UV)^2 - I = U(VU - UV)V + U V U V - U (VU) V
```

is not needed; expand directly:

```text
(UV)^2 - U^2 V^2 = U(VU - UV)V,
U^2 V^2 - I = (U^2 - I)V^2 + (V^2 - I),
```

so

```text
| ||(UV)^2 - I|| - ||UV - VU|| |  <=  ||U^2 V^2 - I||  <=  a + b.
```

Hence `||(UV)^2 - I|| < eta`, `||U^2 - I|| < eta`, `||V^2 - I|| < eta` imply
`||UV - VU|| < 3 eta`, dimension-free. Taking `W = {x, y, xy}` and
`eta = eps/3` realizes `(PLM1)` for `N = 2` and the single relator
`s = [x,y]` presenting `(Z/2)^m`; the remaining relators `x_i^2` are members
of `W` themselves.
