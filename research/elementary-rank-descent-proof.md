---
rg: 2
id: elementary-rank-descent-proof
kind: route
title: Corner-embed the higher rank and recognize its first root as the normal generator
target: elementary-rank-descent-to-two
requires:
  - full-idempotent-ring-has-properly-infinite-unit
  - properly-infinite-unit-rank-two-normal-generator
artifacts:
  - research/artifacts/rank-two-descent-review-2026-09-07.md
---

## Proof

**The half-orthogonal system.**  From `w_iv_j = delta_(ij)` take the `2^k`
words of length `k` in `v_0,v_1` for `S`, and the reversed words in
`w_0,w_1` for `T`; distinct words of the same length give
`T_iS_j = delta_(ij)`.  Keep `m` of them.

**The corner embedding.**  `p = sum_i S_iT_i` is idempotent because
`T_iS_j = delta_(ij)`, and `(1-p)S_k = 0`, `T_j(1-p) = 0`.  Expanding the
product of `jmath(A)` and `jmath(B)` therefore leaves
`(1-p) + sum_(i,l) S_i(AB)_(il)T_l`, so `jmath` is multiplicative, and
`jmath(1) = 1`.  It is injective because `T_i jmath(A) S_j = A_(ij)`.

**Elementary matrices land in rank two.**  For `i != j`,

```text
Psi(e_(ij)(r)) = diag(1 + S_i r T_j, 1) = [e_12(S_i r), e_21(T_j)],
```

the second equality by the prerequisite's commutator identity with
`v = S_i r`, `b = T_j`, whose hypothesis `bv = T_jS_i r = 0` holds since
`i != j`.  These generate `EL_m(R)`, so `Psi(EL_m(R)) <= EL_2(R)`.

**Normal generation.**  `Psi(e_12(1)) = diag(1 + S_1T_2, 1)` is the element
`D` of the prerequisite with `v = S_1`, `w = T_1`, `a = S_2`, `b = T_2`,
whose hypotheses `T_1S_1 = 1`, `T_2S_2 = 1`, `T_2S_1 = 0` hold.  So its
normal closure is `EL_2(R)`.

**The principle.**  Let `rho : EL_2(R) -> C` with the stated triviality at
rank `m`.  Then `rho . Psi` is trivial, so `rho(Psi(e_12(1))) = 1`, and the
kernel of `rho` contains the normal closure of that element, which is all of
`EL_2(R)`.  For `n >= 2`, every root subgroup of `EL_n(R)` lies in a
standard two-coordinate block isomorphic to `EL_2(R)`, on which the
restriction of any such homomorphism is trivial; the root subgroups generate.
