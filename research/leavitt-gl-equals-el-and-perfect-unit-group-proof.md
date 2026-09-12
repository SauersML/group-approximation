---
rg: 2
id: leavitt-gl-equals-el-and-perfect-unit-group-proof
kind: route
title: Transport rank two along the self-similarity, then flatten blocks
target: leavitt-gl-equals-el-and-perfect-unit-group
requires: []
artifacts:
  - GroupApproximation/KOne/AllRanksElementary.lean
  - GroupApproximation/KOne/AllRanksElementaryCore.lean
---

## Direct proof, machine-checked

**All ranks.**  Start from `glTwo_eq_elementary_holds`, the rank-two collapse
supplied by the `K₁` chain.  A binary Leavitt family gives a ring isomorphism
`A ≃+* M_m(A)` for every `m` in the prefix-code family, so `GL_2(M_n(A))` and
`GL_{2n}(A)` are the same group; `EL_p(M_q(A)) = EL_{pq}(A)` is the matching
statement for the elementary subgroups (`AllRanksElementaryCore`).  Composing,
the rank-two collapse over `M_n(A)` becomes `GL_{2n}(A) = EL_{2n}(A)`, which is
every even rank; an odd rank `n` is recovered from `2n` by the same equivalence
run the other way.  Nothing here re-does elimination.

**Perfectness.**  The three-leaf complete prefix code identifies `Aˣ` with
`GL_3(A)`, which the previous paragraph identifies with `EL_3(A)`; in rank at
least three every elementary generator is a commutator of two elementary
generators by the Steinberg relation `[e_{13}(a), e_{32}(1)] = e_{12}(a)`, so
the group is perfect.

**Rank two.**  `binaryLeavittRankTwo_not_isSofic` feeds the two-by-two
Leavitt-corner theorem: `GL_2 = EL_2` from the first item, property `(T)` for
`GL_2` and for the unit group from the property-`(T)` lane.
