---
rg: 2
id: binary-leavitt-unit-group-has-tt-mod-t-proof
kind: route
title: Discharge the four ring hypotheses over the binary Leavitt algebra, then transport rank two to the unit group
target: binary-leavitt-unit-group-has-tt-mod-t
requires:
  - property-tt-mod-t-rigidity-for-elementary-groups
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - GroupApproximation/PropertyTT/PaperStatements.lean
  - GroupApproximation/PropertyTT/FiniteTypeLeavittTT.lean
  - GroupApproximation/Leavitt/LeavittSimplicity.lean
  - GroupApproximation/KOne/AllRanksElementaryCore.lean
---

## Why sufficient

The first prerequisite is the conditional theorem: for a nontrivial finite-type
`F_2`-algebra `R` carrying a binary Leavitt family, single-sandwich division and
a trivial elementary diagonal class, `EL_n(R)` has `(TT)/T` at every rank
`n >= 2` (`finiteType_elementaryGroup_hasTTmodT`, and its free-quotient form
`finiteFreeQuotient_elementaryGroup_hasTTmodT`).  It is consumed by supplying
`R = L_(F_2)(1,2)` and the four hypotheses.  The second prerequisite is the
algebra that turns the resulting elementary group into the unit group.

**Discharging the hypotheses.**  `L` is presented as a quotient of the free
`F_2`-algebra on four generators, so it is nontrivial and of finite type, and
the presentation's generators `x_0, x_1, y_0, y_1` satisfy `y_i x_j = delta_ij`
and `x_0 y_0 + x_1 y_1 = 1`, which is a binary Leavitt family verbatim.
Single-sandwich division is `BinaryLeavitt.exists_mul_mul_eq_one`: for nonzero
`z`, the cylinder partition `sum_(|d| = r) x_d y_d = 1` at the depth `r` of the
deepest `y`-word forces `z x_d != 0` for some `d`, prefix cancellation writes
`z x_d` as a combination of pure `x`-words, and left multiplication by
`y_(g_0)` at a shortest surviving word `g_0`, followed by the killer word
`w = 0^m 1` on both sides, annihilates every other term because `w` and
`e w` are incomparable for every surviving `e`.  The elementary diagonal class
is the `KOne` content named by the second prerequisite: `diag(u,1)` lies in
`EL_2(L)` for every unit `u`.

**Transport to the unit group.**  The second prerequisite supplies
`EL_n(L) = GL_n(L)` at every rank `n >= 2` together with the complete-prefix-code
isomorphism `M_n(L) ~= L`, whose unit form is
`binaryLeavitt_elementaryEquivUnits : EL_n(L) ~= L^x`.  Property `(TT)/T` is a
statement about all unitary representations of the abstract group, so it is
invariant under group isomorphism (`HasTTmodT.of_mulEquiv`); applying it to the
rank-two instance gives `binaryLeavittUnits_hasTTmodT`.

## Not a restatement of either prerequisite

The first prerequisite carries four hypotheses and names no group; this target
has no hypotheses and names one.  The second is an equality of subgroups with
no analysis in it and would remain true verbatim if every quasi-cocycle
statement in the development were deleted; it cannot yield a boundedness
conclusion by itself.  The implication needs both, in that order.
