---
rg: 2
id: olshanskii-sapir-fp-ascending-hnn-of-exponent-n-group
kind: claim
title: For large odd n some finitely presented group is an ascending HNN extension of an infinite group of exponent n
distinct_from:
  grigorchuk-ascending-hnn-extension-is-finitely-presented: that is Grigorchuk's amenable example over a 2-group of unbounded exponent; this is the Ol'shanskii–Sapir non-amenable example over a group of bounded exponent n.
---

**ESTABLISHED** (literature import, `olshanskii-sapir-fp-ascending-hnn-of-exponent-n-group-citation`).

For every sufficiently large odd `n` there is a finitely presented group `𝒢`
that is an ascending HNN extension of a finitely generated infinite group `H̄`
of exponent `n`. It is an extension of a non-locally-finite group of exponent
`n` by an infinite cyclic group, contains the free Burnside group `B(2,n)`, and
is non-amenable without non-cyclic free subgroups.

**The data.**

- `ℋ = < c_1, ..., c_m | ℛ >` is a finitely presented group containing a
  CEP-embedded free Burnside group `B_b(m,n)` with free basis
  `b_i = w_i(c_1, ..., c_m)`.
- `H̄ = < c_1, ..., c_m | ℛ ∪ 𝒱 ∪ ℛ' >`, where `𝒱` is the set of all `n`-th
  powers and `ℛ'` the derived words `r^{(k)}(c) = r(w^{(k)}(c))`, `k >= 1`.
- `c_i -> b_i` is an isomorphism of `H̄` onto its subgroup `B̄ = < b_1, ..., b_m >`.
- `𝒢 = < H̄, t | t c_i t^-1 = b_i > = < c_1, ..., c_m | ℛ ∪ 𝒰 >`, with
  `𝒰 = { t c_i t^-1 w_i^-1 }`.

With stable letter `s = t^-1`, the endomorphism is `phi(c_i) = w_i(c)`, which is
injective with image `B̄`.
