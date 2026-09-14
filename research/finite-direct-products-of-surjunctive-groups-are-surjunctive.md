---
rg: 2
id: finite-direct-products-of-surjunctive-groups-are-surjunctive
kind: claim
title: The direct product of two surjunctive groups is surjunctive
distinct_from:
  products-with-lef-factors-preserve-surjunctivity: that is the proved case where one factor is LEF; this is the unrestricted product of two surjunctive groups, which the rectangle-clause axiomatization does not give because its conclusions are disjunctions.
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

**OPEN.** If `G` and `K` are surjunctive, then `G x K` is surjunctive.

**Equivalent forms** (Section 3 of the artifact):
- **All products.** It is equivalent to closure under arbitrary unrestricted direct products: a finite
  subset of a product embeds into a finite subproduct by a projection, and the table-realization
  corollary finishes.
- **Graph products.** It is equivalent to `graph-products-of-surjunctive-groups-are-surjunctive`, which
  includes free products.
- **Quasivariety.** It is equivalent to the surjunctive class being a quasivariety, axiomatized by
  quasi-identities. The class already contains the trivial group and is closed under isomorphic copies,
  subgroups and ultraproducts, so Mal'cev's characterization leaves only products.

**Proved cases.**
- **LEF factor:** `products-with-lef-factors-preserve-surjunctivity`.
- **Known witnesses:** products of permutational wreaths with residually finite lamps over residually
  finite bases.
- **Tester host:** the tester `U` of `gottschalk-surjunctivity-fixed-two-generator-tester` contains
  `U x U`, so its products add nothing.

The conjecture implies the claim. A failure would be a Gottschalk counterexample of product shape, whose
certificate sits across both factors.

## Attempts

- **Coset transplant along one factor.** Separating finite sets needs subgroups `G_0 x {1}`.
  - With `G_0` of infinite index, the fibre alphabets are infinite, and injective non-onto maps then exist
    over every group (Remark A.1 of the artifact).
  - With `G_0` of finite index, `G` must be residually finite, which is the LEF case again.
- **Table transfer.** Conclusions of rectangle clauses are disjunctions of equations. The reverse
  inequality of a certificate on `G x K` can use both coordinates, so neither factor inherits a
  certificate (remark (d) of the rectangle-clause artifact).
- **Counting in one factor.** It needs Følner or sofic structure in that factor and finitely many rows
  in the other. Neither is available for two nonsofic factors.
- **First open test instance.** Two surjunctive groups with no LEF factor and no wreath structure, for
  example two finitely presented surjunctive nonsofic doubles of Kun–Thom pairs.
