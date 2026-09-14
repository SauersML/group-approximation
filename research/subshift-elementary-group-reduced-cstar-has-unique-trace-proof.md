---
rg: 2
id: subshift-elementary-group-reduced-cstar-has-unique-trace-proof
kind: route
title: Unique trace for the subshift elementary groups from BKKO concentration
target: subshift-elementary-group-reduced-cstar-has-unique-trace
requires: [bkko-reduced-traces-concentrate-on-amenable-radical, subshift-elementary-group-is-simple-modulo-centre, crossed-product-el-kazhdan-iff-finite-field-and-subshift]
---

1. Over `F_2` the centre of `G = EL_n(LC(X,F_2)⋊Z)` is trivial, so `G` is simple (`subshift-elementary-group-is-simple-modulo-centre`). Over `F_q`, pass to `G/Z`.
2. `G` has property (T) (`crossed-product-el-kazhdan-iff-finite-field-and-subshift`) and is infinite, so it is nonamenable: an amenable Kazhdan group is finite.
3. The amenable radical is an amenable normal subgroup. By simplicity it is `{e}` or `G`, and step 2 excludes `G`.
4. By BKKO Theorem 4.1 (`bkko-reduced-traces-concentrate-on-amenable-radical`), every tracial state `τ` satisfies `τ(λ_s) = 0` for `s ∉ R_a(G) = {e}`. So `τ` is the canonical trace.
