---
rg: 2
id: fpbs-residual-class-has-torsion-products
kind: claim
title: Products of two infinite groups with only finite amenable subgroups lie in the residual fixed-price-one non-acylindrically-hyperbolic class
distinct_from:
  fpbs-product-no-amenable-wq-normal: that is the open percolation claim for these products; this is the group-theoretic membership lemma placing them in the residual class, with no percolation content.
  fpbs-product-amenable-subgroup-wq-normal: that shows products with an infinite amenable subgroup in a factor have an amenable wq-normal subgroup; this is the opposite case, where the factors have only finite amenable subgroups and the product meets every hypothesis of the residual class.
---

**ESTABLISHED.** Let `H` and `K` be infinite finitely generated groups whose
amenable subgroups are all finite. Then `G = H x K` is finitely generated and
nonamenable, and it has no infinite amenable subgroup. It has fixed price one
and is not acylindrically hyperbolic. So `G` satisfies all three hypotheses of
`fpbs-residual-price-one-non-ah-class-nonuniqueness`.

**The residual class is nonempty.** By
`fpbs-monster-groups-have-only-finite-amenable-subgroups` it contains, for
example, `T x T'` for Ol'shanskii torsion Tarski monsters `T` and `T'`, and
`B(m,n) x B(m',n')` for `m, m' >= 2` and odd `n, n' >= 1003`. Mixed products
such as `T x B(m,n)` are also members.

Every member found this way is a torsion group with no infinite amenable
subgroup. So it lies in part (R0) of `fpbs-wq-normal-hull-is-almost-malnormal`.
No member of part (R1) is known.
