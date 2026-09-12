---
rg: 2
id: leavitt-gl-equals-el-and-perfect-unit-group
kind: claim
title: Over a binary Leavitt algebra GL equals EL at every rank and the unit group is perfect
distinct_from:
  d-ary-leavitt-groups-nonsofic-over-finite-fields: That is a nonsoficity statement about the same groups; this is pure algebra -- an identification of GL with EL and perfectness -- with no approximation property in it, and it is what lets the nonsoficity statements move between ranks.
  universal-leavitt-el4-nonsofic: That is the rank-four nonsoficity endpoint; this is the rank transport underneath it, and it also closes the rank-two form.
  openai-leavitt-unit-nonsofic: That is the nonsoficity of the binary Leavitt unit group; this asserts nothing about soficity -- it identifies GL with EL and proves the unit group perfect, both by internal algebra -- and it is what carries property (T) between the ranks that node's configuration uses.
  kl-violating-equation-over-leavitt-unit-group: That asks for a Kervaire-Laudenbach-violating equation over the same unit group, which would refute its hyperlinearity and is open; this is the group-theoretic structure of that unit group and supplies no equation.
artifacts:
  - GroupApproximation/KOne/AllRanksElementary.lean
  - GroupApproximation/KOne/AllRanksElementaryCore.lean
  - GroupApproximation/Leavitt/PrefixCode.lean
---

ESTABLISHED, and internal throughout -- no external `K`-theory input.
`KOne/AllRanksElementary`:

* `glAll_eq_elementary n (hn : 2 ≤ n)` -- `GL_n(L) = EL_n(L)` for every rank
  `n ≥ 2` and every field.  No new Gaussian elimination is performed: the
  prefix-code self-similarity `A ≃+* M_m(A)` and the block flattening
  `EL_p(M_q(A)) = EL_{pq}(A)` carry the rank-two collapse
  (`glTwo_eq_elementary_holds`, from the `K₁` chain) up to `EL_{2n}` and back
  down to `EL_n` -- even ranks from rank two, every rank from its double;
* `binaryLeavittUnits_perfect` -- `L_k(1,2)ˣ` is perfect, since the three-leaf
  prefix code identifies the unit group with `GL_3 = EL_3` and every elementary
  generator is a commutator by the Steinberg relation;
* `binaryLeavittRankTwo_not_isSofic` -- the rank-two Leavitt-corner theorem
  instantiated over `L_k(1,2)` for every finite field, all three of whose
  hypotheses (`GL_2 = EL_2`, and property `(T)` for `GL_2` and for the unit
  group) are closed theorems here.

## Why it is worth a node of its own

It is the reason the nonsoficity statements do not have to be re-proved rank by
rank: every rank-transport step in
[[d-ary-leavitt-groups-nonsofic-over-finite-fields]] and
[[universal-leavitt-el4-nonsofic]] is an instance of the identification above
or of the prefix-code equivalence beside it.  Perfectness is independent of all
of that and is a structural fact about the unit group.
