---
rg: 2
id: dyadic-extensive-amenability-if-jones-subgroup-coamenable
kind: claim
title: If Jones' subgroup is co-amenable in Thompson's group F, then F acts extensively amenably on the dyadic rationals
distinct_from:
  jones-subgroup-coamenable-if-dyadic-action-extensively-amenable: that is the converse implication, from extensive amenability to co-amenability; this goes from co-amenability back to extensive amenability.
  thompson-f-dyadic-action-is-extensively-amenable: that is the unconditional extensive amenability; this derives it from co-amenability of the oriented subgroup.
  jones-subgroup-is-co-amenable-in-thompson-f: that is the co-amenability itself; this is an implication out of it.
---

**ESTABLISHED.** Let `\vec F ≤ F` be Jones' oriented subgroup and `D ⊂ (0,1)` the dyadic rationals. If
`F/\vec F` carries an `F`-invariant mean, then `F ↷ D` is extensively amenable.

**Key computation.** Let `S ⊂ D` be the dyadics with odd binary digit sum, so `\vec F = Stab_F(S)`. Every
translate `gS` differs from `S` by a set `gS Δ S` with finitely many jumps at dyadic points, and
`c(g) = ∂(gS Δ S)` is a 1-cocycle `F → P_f(D)`. For `h ∈ F`, `x ∈ ∂(h⁻¹S Δ S)` exactly when
`n(hx) − n(x) + log₂ h'(x⁻)` is odd, where `n` is binary length. On the stabilizer `F_x` this is the parity
of `log₂ h'(x⁻)`, a nontrivial point character.

**Consequence.** Every `F`-invariant mean on `F/\vec F` gives weight `1/2` to each boundary point. The
difference of two independent copies of the mean is untwisted, and iterated unions upgrade it to an
extensive-amenability mean.

Proof route: `dyadic-extensive-amenability-from-jones-means-proof`.
