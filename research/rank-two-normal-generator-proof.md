---
rg: 2
id: rank-two-normal-generator-proof
kind: route
title: Reach the complementary summand by an involution exchanging two equivalent idempotents
target: properly-infinite-unit-rank-two-normal-generator
requires: []
artifacts:
  - research/artifacts/rank-two-descent-review-2026-09-07.md
---

## Proof

**The commutator.**  Multiplying out
`e_12(v)e_21(b)e_12(v)^(-1)e_21(b)^(-1)`, the `(1,1)` entry is
`(1+vb)^2 - vb = 1 + vb + v(bv)b = 1 + vb` and the other three entries
collapse on `bv = 0`, giving `D = diag(1+vb,1)`.  Also
`(1+vb)(1-vb) = 1 - v(bv)b = 1`, so `1+vb` is a unit.

**The image of `v`.**  `D e_12(x) D^(-1) = e_12((1+vb)x)`, so

```text
[D, e_12(ar)] = e_12((1+vb)ar - ar) = e_12(v(ba)r) = e_12(vr),
```

and every `e_12(vr)` lies in the normal closure `N`.

**The complement.**  Put `f = 1 - vw`.  Then `f^2 = f`, `fv = 0`, `wf = 0`,
and `vfw` is an idempotent orthogonal to `f`, equivalent to it through
`vf` and `fw`, since `(fw)(vf) = f(wv)f = f` and `(vf)(fw) = vfw`.  Set

```text
z = vf + fw + 1 - f - vfw.
```

The three summands `1-f-vfw`, `vf`, `fw` annihilate one another in the
pattern of an exchange: `(vf)^2 = (fw)^2 = 0`, `(vf)(fw) = vfw`,
`(fw)(vf) = f`, and `1-f-vfw` kills both on either side.  So `z^2 = 1` and
`zf = vf`.

Since `z` is a unit with `z^(-1) = z`, the Whitehead factorization

```text
diag(z,z^(-1)) = e_12(z)e_21(-z^(-1))e_12(z)e_12(-1)e_21(1)e_12(-1)
```

puts `h = diag(z,z)` in `EL_2(R)`.  Then

```text
h e_12(fr) h^(-1) = e_12(zfrz) = e_12(vfrz) in N,
```

so `e_12(fr) in N`.  From `r = vwr + fr`,
`e_12(r) = e_12(vwr)e_12(fr) in N`, and conjugating by the elementary
signed permutation gives the lower roots.  So `N = EL_2(R)`.

**The count.**  `e_12(vr)` is a product of two conjugates of `D^(+-1)` by
the commutator above; `e_12(fr)` is a conjugate of such a product, so also
two; their product gives four for an arbitrary upper root, and conjugation
gives the same bound for a lower root.
