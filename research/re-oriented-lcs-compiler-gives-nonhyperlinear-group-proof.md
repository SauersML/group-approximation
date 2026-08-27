---
rg: 2
id: re-oriented-lcs-compiler-gives-nonhyperlinear-group-proof
kind: route
title: A proof-search fixed point explicitly keeps J on the nonhalting side
target: re-oriented-lcs-compiler-gives-nonhyperlinear-group
requires:
  - perfect-lcs-gap-implies-nonhyperlinear
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Given `e`, enumerate formal consequences of the finite presentation output
for `M_e` and halt exactly when a proof of `J_e=1` appears.  The effective
recursion theorem gives `e_*` whose machine performs this search for its own
output presentation.  It cannot halt: a stopping proof gives `J_(e_*)=1`,
whereas halting-side perfect commuting completeness gives `J_(e_*)!=1`.
It also cannot have `J_(e_*)=1`, because
then completeness of proof enumeration would make it halt.  Hence it is a
specific nonhalting machine with `J_(e_*)!=1`.

Nonhalting-side strict soundness keeps its quantum value below one, while the
nontrivial central mark gives perfect commuting value.  The established
`perfect-lcs-gap-implies-nonhyperlinear` converts its explicitly computed
finite solution-group presentation into the desired witness.
