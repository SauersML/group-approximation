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
- **Update (w3-products, 2026-09-12): that test instance is covered.** Finitary split structures pass to
  products over the product base (`finitary-split-structures-pass-to-direct-products`). For a fixed
  surjunctive `G`, the class of second factors `K` with `G x K` surjunctive contains the LEF permanence
  closure: LEF groups, subgroups, local embeddings, finitary split extensions and graph folds
  (`products-with-lef-permanence-closure-factors-are-surjunctive`). So `D x D` for Kun–Thom doubles `D`,
  and `G x W`, `G x D` for every surjunctive `G`, are surjunctive. The claim stays open only for two factors
  outside that closure. That includes every group containing a finitely presented simple nonsofic FA
  subgroup, such as `R^x` and the tester `U`.
- **Fibre plus compactness (w3-products).** Reading `A^(G x H)` as `(A^H)^G` makes `tau` an automaton over
  `G` with the compact alphabet `A^H`. Truncating to a finite window `E` of `H` gives a self-map only when
  `E M_H ⊆ E`, which fails for infinite `<M_H>`. Closing the device needs exact finite total realizations of
  the `H`-coordinate tables, which is LEF data, so it reaches the closure theorem above and no further.
  Sofic realizations break the decoder identity on a positive fraction of points, and the repair is a count
  over an infinite `G`-direction alphabet. Artifact
  `research/artifacts/w3-products-permanence-closure-2026-09-12.md`, Section 3.
- **Repairing the sofic device (w4-free-pos-b, 2026-09-12).**
  - **The repair.** Store the input on the `epsilon |V|` bad points of a sofic model in an extra track.
    The transplanted automaton over `G` is then injective, at a cost of `q^(epsilon |V|)` output symbols.
  - **Single-fibre patterns.** If a Garden of Eden pattern lies in one fibre `{g} x K`, it compresses every
    output column by `(1 - q^(-|E|))^(c|V|)`, and the device closes. So strict automata over
    `G x K`, with `G` surjunctive and `K` sofic, have every Garden of Eden pattern across two fibres
    (`strict-product-automata-have-no-single-fibre-garden-of-eden`).
  - **Multi-fibre patterns.** The device yields an injective automaton into `n` copies of a proper subshift
    times a slightly larger full shift. Closing it needs quantitative surjunctivity of `G`
    (`sofic-factor-products-via-quantitative-surjunctivity`), which sofic groups have.
  - Artifact `research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md`.
