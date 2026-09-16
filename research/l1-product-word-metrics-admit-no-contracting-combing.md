---
rg: 2
id: l1-product-word-metrics-admit-no-contracting-combing
kind: claim
title: A product of two infinite groups, with the union of factor generating sets, admits no contracting combing
distinct_from:
  amenable-automatic-groups-admit-contracting-combings: that is the open claim that some generating set of each amenable automatic group carries a contracting combing; this shows that for the l1 product generating set of a product of infinite groups no combing is contracting, so the generating set cannot be kept arbitrary
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem that Z^n with the standard generators has contractible Rips complexes; this shows that the same word metric admits no contracting combing for n >= 2, so Alonso's theorem cannot give that result
  contractible-rips-groups-closed-under-direct-products: that builds contractible Rips complexes of products for the l-infinity product generating set; this is an obstruction to contracting combings for the l1 product generating set
artifacts:
  - research/artifacts/zaremsky-4-01-contracting-combings-2026-09-16.md
---

**ESTABLISHED** (route `l1-product-word-metrics-admit-no-contracting-combing-proof`).

Let `G` and `H` be infinite groups with finite generating sets `S_G` and `S_H`. Give
`G × H` the generating set `(S_G × {1}) ∪ ({1} × S_H)`, whose word metric is
`d_G + d_H`. Then no combing of `G × H` is contracting in the sense of
`contracting-combings-give-contractible-rips-complexes`, for any constant `C >= 2`.

**Consequences.**
- For `d >= 2`, `Z^d` with the standard generators `{±e_1, ..., ±e_d}` admits no
  contracting combing.
- If `Γ` is a join of two nonempty finite graphs, the right-angled Artin group `A_Γ`
  with its standard generators admits none. This includes `F_2 × F_2`.
- Whether a group admits a contracting combing depends on the generating set.
  `Z^2` has one for `{−1,0,1}^2 ∖ {0}` (`linf-lattice-groups-admit-contracting-combings`)
  and none for `{±e_1, ±e_2}`.

So an attack on `amenable-automatic-groups-admit-contracting-combings` that keeps
the generating set of a given automatic structure and improves its combing cannot
work in general: `Z^2` is automatic over `{±e_1, ±e_2}`.
