---
rg: 2
id: property-t-free-st20-collapse-transfers-to-el12-proof
kind: route
title: Project St20 onto EL20 and apply the explicit all-positive-rank Leavitt equivalence
target: property-t-free-st20-collapse-transfers-to-el12
requires: []
artifacts:
  - GroupApproximation/Steinberg/Basic.lean
  - GroupApproximation/Leavitt/PrefixCode.lean
  - GroupApproximation/Leavitt/LeavittRankEquivalence.lean
  - GroupApproximation/Sofic/FullRadicalClosureProperties.lean
---

Write `pi : St_20(R) -> EL_20(R)` for
`SteinbergGroup.projection`.  It is surjective by
`SteinbergGroup.projection_surjective`.  Functoriality of the genuine-corona
MF radical therefore gives

```text
Rad_MF(St_20(R)) = top  ==>  Rad_MF(EL_20(R)) = top;
```

this is the elementary `map(top)=top` argument packaged in
`actualCoronaMFResidual_eq_top_of_surjective`.

The universal binary Leavitt family has, for every complete left-comb prefix
code, an explicit ring equivalence `M_n(R) ~= R`.  Flattening coefficients
gives the group equivalence

```text
LeavittFamily.rankSuccEquiv : EL_(a+1)(R) ~= EL_(b+1)(R)
```

for all positive `a,b`.  Instantiate it at `a=19`, `b=11` to obtain
`EL_20(R) ~= EL_12(R)`.  Full MF radical is invariant under a group
equivalence, again by the surjective-image theorem.  Composing the two steps
proves the implication.

The definition `rankSuccEquiv` is earlier than, and independent of, the
Property-`(T)` transfer theorem that happens to share its current source file.
A dependency-clean Lean endpoint should move or restate that definition in an
algebra-only module, but no new mathematical input is required.

