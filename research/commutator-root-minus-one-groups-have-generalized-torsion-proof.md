---
rg: 2
id: commutator-root-minus-one-groups-have-generalized-torsion-proof
kind: route
title: Two shifts of the relation write y_2 and y_1 as products of a conjugate of y with a positive power of the other letter; eliminating y_1^K leaves a positive product of conjugates equal to 1
target: commutator-root-minus-one-groups-have-generalized-torsion
requires:
  - commutator-root-frontier-kills-pl-and-bi-ordered-targets
---

## Item 1: the identity

The relation of `G(K; -1, 1)` is `y_1^K = [y_0^{-1}, y_2] = y_0 y_2^{-1} y_0^{-1} y_2`, and the same with every index
shifted.
- At shift 0 it gives `y_0 y_2^{-1} y_0^{-1} = y_1^K y_2^{-1}`. Inverting both sides, `P_1 = y_0 y_2 y_0^{-1} = y_2 y_1^{-K}`,
  that is, `y_1^K = P_1^{-1} y_2`.
- At shift 1 it gives `y_2^K = y_1 y_3^{-1} y_1^{-1} y_3`, so `y_3^{-1} y_1^{-1} y_3 = y_1^{-1} y_2^K`. Inverting,
  `P_2 = y_3^{-1} y_1 y_3 = y_2^{-K} y_1`, that is, `y_1 = y_2^K P_2`.
- Hence `P_1^{-1} y_2 = y_1^K = (y_2^K P_2)^K`, so `1 = P_1 (y_2^K P_2)^K y_2^{-1}`.
- Split the last factor as `y_2^K P_2 y_2^{-1} = y_2^{K-1} · (y_2 P_2 y_2^{-1})`. This gives

  `1 = P_1 · (y_2^K P_2)^{K-1} · y_2^{K-1} · (y_2 P_2 y_2^{-1})`.

Every factor is a conjugate of `y`: `P_1` of `y_2`, `P_2` of `y_1`, and `y_2` itself. The count is
`1 + (K-1)(K+1) + (K-1) + 1 = K^2 + K`. `gt_identity.py` checks the word exactly for `K ≤ 5` with the
Britton-lemma word problem of `tower_wp.py`.

**Consequence.** Apply `φ`. The image is a product of conjugates of `φ(y)` equal to `1`. So if `φ(y) ≠ 1`, then
`φ(y)` is generalized torsion. A bi-orderable group has no generalized torsion, since a product of conjugates of a
positive element is positive. This recovers item 4 of
[[commutator-root-frontier-kills-pl-and-bi-ordered-targets]] for `(-1, 1)` and extends it to R*-groups. ∎

## Item 2: the ball test

`bo_sat.py K α β perms W r` works as follows.
- It enumerates the freely reduced words of length at most `r` in `y_0, …, y_{W-1}`.
- It buckets them by a hash of their images in the largest 24 permutation quotients of index at most 9
  (`lowindex.g`). It merges two words only when `tower_wp` proves them equal.
- It then writes the clauses of item 2 of the claim. Each product, conjugate or shift is located by hash and
  confirmed by `tower_wp` before its clause is added. So every clause is a true consequence of a `t`-invariant
  bi-order of `N`, and an UNSAT answer would be a proof of non-bi-orderability.
- A bi-order of `G` restricts to one of `N` that is invariant under conjugation by `t`, which is the index shift.
- It is solved with CaDiCaL (pysat). SAT answers only say that the ball does not certify anything.
