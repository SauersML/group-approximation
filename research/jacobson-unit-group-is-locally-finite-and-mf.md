---
rg: 2
id: jacobson-unit-group-is-locally-finite-and-mf
kind: claim
title: The binary Jacobson unit group is the direct limit of the finite general linear groups over F_2, hence MF, although the ring is not directly finite
distinct_from:
  properly-infinite-unit-group-is-not-mf: that proves a unit group is NOT MF when the defect is full; this computes the unit group of a ring whose defect is not full and finds it IS MF, so it is the counterexample showing that fullness hypothesis cannot be dropped.
  binary-jacobson-matrix-rings-have-no-infinite-corner: that rules out properly infinite idempotents in every finite matrix ring over the same algebra, from the symbol and the finitary corner; this computes the unit group, and recovers only the one-by-one case of that statement, by a different route through the corner unitization.
  finite-additive-order-one-sided-defects-are-mf-invisible: that makes every elementary group of rank at least four over this ring non-MF; this shows the rank-one group is MF, so the two together prove that no embedding of GL_4 into the unit group exists.
  binary-leavitt-all-ranks-full-mf-radical: that is the Leavitt unit group, where the defect is full, the unit group coincides with the elementary groups, and full collapse holds; this is the Jacobson algebra, where the defect is not full and the opposite conclusion holds.
artifacts:
  - research/artifacts/jacobson-unit-group-and-rank-four-recheck-2026-09-08.md
---

**ESTABLISHED.** Let `J = F_2<s,t | ts = 1>` and `e = 1 - st != 0`.
Then

```text
J^x = union_N GL_N(F_2)
```

along the identity-block inclusions. So `J^x` is countable, locally
finite and **MF**, while `J` is not directly finite.

**Consequences.**

* The rank-one statement is **false**: `R^x` MF does not imply `R`
  directly finite. The fullness hypothesis of
  `properly-infinite-unit-group-is-not-mf` and the properly-infinite
  corner of `properly-infinite-corner-forces-non-mf-from-rank-two`
  cannot be weakened to a nonzero defect, and the counterexample sits
  inside this archive's own running example.
* `J` has no nonzero properly infinite idempotent. Otherwise the
  rank-two corner theorem plus
  `corner-unitization-embeds-elementary-groups` and `v |-> 1 - p + v`
  would put a non-MF group inside `J^x`. This is the `d = 1` case of
  `binary-jacobson-matrix-rings-have-no-infinite-corner`, reached
  independently; the general `d` is not recovered, since MF-ness of
  `J^x` says nothing directly about `GL_d(J)`.
* With `finite-additive-order-one-sided-defects-are-mf-invisible`,
  which makes `E_n(J)` non-MF for `n >= 4`, there is **no embedding
  of `GL_4(J)` into `J^x`**. Sizes two and three remain open.

The proof is a symbol-and-index computation, not an approximation
argument: the symbol quotient is `F_2[z,z^-1]`, a unit has symbol
`z^k`, and comparing `dim V/V_N = N` with `dim V/V_(N+k) = N+k`
forces `k = 0`, after which every unit is a finite invertible block
extended by the identity.

DERIVATION
jacobson-unit-group-symbol-and-index-proof
