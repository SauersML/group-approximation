---
rg: 2
id: prime-characteristic-jacobson-embedding-proof
kind: route
title: Extract a matrix coefficient and invert it in the prime field
target: prime-characteristic-defect-embeds-the-jacobson-algebra
requires:
  - jacobson-shift-representation-is-faithful
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Proof

Let `a != 0` lie in the kernel of `(PC2)`.  By the prerequisite the
standard shift representation of `J_(F_p)` is faithful, so `a` has a
nonzero matrix coefficient `c in F_p`, say the coefficient of `v_i` in
`a v_j`, and the coefficient extraction identity `(JSF3)` holds:

```text
Q T^i a S^j Q = c Q      in  J_(F_p).
```

Apply the ring map.  Its value on `Q = 1 - ST` is `1 - st`, and the image
of `a` is zero, so

```text
0 = c (1 - st)   in R.
```

`R` has characteristic `p` and `c` is a nonzero element of `F_p`, hence
invertible there, so `1 - st = 0`, contradicting `(PC1)`.  Therefore the
kernel is zero.

Entrywise extension of an injective unital ring map is injective on
matrices and carries elementary generators to elementary generators, so
`EL_n(J_(F_p)) -> EL_n(R)` is injective for every `n >= 2`.

## The equivalence for a fixed characteristic

If `EL_n(J_(F_p))` is non-MF then so is every `EL_n(R)` containing it as
a subgroup, by the subgroup permanence of MF.  Conversely `J_(F_p)`
itself is a ring of characteristic `p` with `ts = 1 != st`, so it is one
of the rings in the class.  Hence the class question and the single case
coincide.
