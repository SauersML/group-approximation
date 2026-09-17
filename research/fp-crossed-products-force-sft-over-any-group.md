---
rg: 2
id: fp-crossed-products-force-sft-over-any-group
kind: claim
title: If the crossed-product algebra of a subshift over any finitely generated group is finitely presented, the subshift is of finite type
distinct_from:
  fp-subshift-crossed-products-are-sfts: that is the case P = Z^2, using the commutation relations of Z^2 in the normal form; this is every finitely generated group, using only monomial bookkeeping in the free group on the generators.
  fp-alternating-full-groups-of-free-subshifts-force-sft: that concerns finite presentation of alternating full groups of free subshifts; this concerns finite presentation of the crossed-product algebra, for arbitrary subshifts.
  sft-crossed-product-fp-iff-quantum-rigid: that characterizes finite presentation among Z^2 SFTs; this shows that, over every finitely generated group, nothing outside SFTs is finitely presented.
artifacts:
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
---

**ESTABLISHED (unreviewed).** Let `P` be a finitely generated group, `A` a finite alphabet,
`X ⊆ A^P` a nonempty subshift and `k` a field. If `LC(X, k) ⋊ P` is finitely presented as a
`k`-algebra, then `X` is a subshift of finite type. More precisely, if `n` bounds the degrees of the
relators in the generators `e_a = χ[x(1) = a]` and `u_s` (`s` in a finite symmetric generating set),
then `X` is defined by forbidding the `n`-ball patterns that do not occur in `X`.

**Why it matters.** Over any acting group, a finitely presented Cantor crossed-product host in
`decidable-group-algebras-have-fp-cantor-crossed-hosts` is an SFT crossed product. With
`free-group-sft-host-units-have-doubly-exponential-wp` this kills every free acting group
(`free-group-cantor-crossed-products-are-not-universal-hosts`).

DERIVATION
fp-crossed-products-force-sft-over-any-group-proof
