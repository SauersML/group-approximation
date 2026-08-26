---
rg: 2
id: fixed-ambient-subgroup-levels-proof
kind: route
title: Embed the countable free product of each two-generator family into V and read the subgroup off its two words
target: fixed-ambient-subgroup-levels-rf-amenable-t
requires:
  - residual-finiteness-two-generator-recursive-is-pi3-complete
  - amenability-two-generator-recursive-is-pi2-complete
  - kazhdan-property-t-of-finite-presentations-is-sigma1-complete
  - mikaelian-explicit-higman-embedding
---

Each of the three cited theorems produces a computable family of
two-generator recursive presentations `e |-> G_e` whose group has the
property iff `e` lies in a `Pi^0_3`-, `Pi^0_2`-, respectively
`Sigma^0_1`-complete set (the shift right-angled Artin family with dyadic
rows, the same family with `J_e = {j+1 : j in W_e}`, and the
two-generator `SL_3(Z)`-or-`SL_3(Z) x Z` family).  The countable free
product `*_e G_e` is recursively presented uniformly, embeds in a finitely
presented group by [[mikaelian-explicit-higman-embedding]] and hence in
`V`, and the image of the generating pair of `G_e` is a pair of words
`(u_1(e), u_2(e))` computable from `e` generating a copy of `G_e`.  This
gives the hardness; the upper bounds are those of the recursive
presentations (the induced presentation of `<u_1, u_2> <= V` is recursive
uniformly): `Pi^0_3` for residual finiteness, `Pi^0_2` for amenability
(Kesten on the two generators), `Sigma^0_1` for property (T) (Ozawa on the
two generators).
