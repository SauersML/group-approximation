---
rg: 2
id: non-weakly-sofic-via-leavitt-chromatic-commutator-code
kind: route
title: A bounded-area chromatic commutator code at the marked Leavitt root makes the Steinberg group non-weakly-sofic
target: non-weakly-sofic-group-exists
requires:
  - binary-leavitt-bounded-area-chromatic-code
  - chromatic-codes-kill-marks-in-every-bi-invariant-approximation
---

This is a hardness-transfer bridge.  It records that the leaf
`binary-leavitt-bounded-area-chromatic-code` of the Property-(T)-free Leavitt
route `property-t-free-leavitt-via-chromatic-code` would also settle
Glebsky--Rivera Conjecture 4.5.

**The mark is nontrivial.**  Take

```text
Delta = St_20(L_(F_2)(1,2)),      z = x_13(s_1 t_1).
```

Use the convention `t_i s_j = delta_(ij)`, `sum_i s_i t_i = 1`.  Then
`e = s_1 t_1` satisfies `e s_1 = s_1`.  Moreover `s_1 != 0`, since
`L_(F_2)(1,2)` acts on the `F_2`-space with basis the infinite binary
sequences `x`, by `s_i(x) = ix` and `t_i(jx) = delta_(ij) x`.  These
operators satisfy both relations, and `s_1` is nonzero there.  So `e != 0`.

The Steinberg map `x_ij(r) -> I + r E_ij` sends `z` to `I + e E_13`, which is
not `I`.  Hence `z != 1` in `Delta`.

**The bridge.**  Suppose `binary-leavitt-bounded-area-chromatic-code` holds:
the fixed finite presentation of `Delta` carries words satisfying
`(CCC1)-(CCC2)` around `z`.  Then (BI4) of
`chromatic-codes-kill-marks-in-every-bi-invariant-approximation` says that
the countable group `Delta` is not weakly sofic.

The same hypothesis makes `Delta` non-hyperlinear
(`nonhyperlinear-via-leavitt-chromatic-commutator-code`).  So the leaf is at
least as hard as both roots.
