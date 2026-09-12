---
rg: 2
id: atlas-first-rank-five-relator-kills-order-one-weyl-slice
kind: claim
title: The first rank-five relator has no order-one Weyl phase solution
---

**ESTABLISHED.**  For the first relation in the deterministic usable packet,

```text
s = root_12_1e,
```

the exact balanced-area collector gives the constant Laurent polynomial

```text
f_s(t) = 16953689 / 41287680.                         (AWK1)
```

There are no other nonzero balanced-area coefficients.  Consequently

```text
f_s(t)-1 = -24333991 / 41287680,                     (AWK2)
```

and the one-relation gcd is already `1`.  The exported exact Bezout
certificate is

```text
(-41287680 / 24333991) (f_s(t)-1) = 1.               (AWK3)
```

Thus no complex `t`, and in particular no non-torsion unit-circle phase, can
satisfy the complete order-one Weyl/common-root system.  The route
`atlas-three-label-mode-rotation-common-root` is refuted by this single literal
relation.  This does **not** exclude arbitrary non-Heisenberg pairs of two
coefficient unitaries in the general moment reduction.

### Exact computation provenance

MSI job `17081560` completed in 54 seconds with peak RSS 200,356 KB.  It used
one CPU and no dense regular-`A8` matrix.  The packet hash is

```text
9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99,
```

the one-row balanced-table hash is

```text
bd205a6f30584f8f2edaecded6f9b98228573f3277333661118a72b05c5aeafd,
```

and the fetched artifact is
`experiments/atlas-rank5-balanced-area.json`.  A second remote verifier
reconstructed `(AWK2)` from the sparse coefficient row, multiplied it by the
exported Bezout coefficient, and checked exact equality with `1` using rational
arithmetic.  The job log contains `SENTINEL_ATLAS_BAT1_DONE`.
