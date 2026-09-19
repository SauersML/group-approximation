---
rg: 2
id: stw82-separable-extension-maximum
kind: claim
title: Nuclear dimension is the maximum across every separable C*-extension
---

For every extension of separable C*-algebras

```text
0 -> I -> E -> D -> 0,
```

the nuclear dimension of `E` is the maximum of the nuclear dimensions of
`I` and `D`.

## Attempts

The nonseparable case reduces to this claim by
`stw82-every-counterexample-reflects-to-a-separable-subextension`.  For a
general separable extension, the Winter--Zacharias quasicentral cut gives
the sum-plus-one bound.  Reusing the endpoint colours requires
orthogonality that is presently available only in the special cases listed
at `stw99-problem-lxxxii-nuclear-dimension-extensions`; no general source of
that orthogonality is known.  The route cannot simply perturb the raw
complementary cutdowns: `stw82-complementary-cutdowns-merge-iff-near-projections`
identifies that move with the near-projection regime, while
`stw82-commutative-max-formula-with-maximal-cutdown-overlap` gives a positive
commutative extension where every quasicentral approximate unit has the
maximal possible overlap `1/4`.
