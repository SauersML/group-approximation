---
rg: 2
id: v-times-golden-silver-wang-product-full-group-is-not-fp-proof
kind: route
title: Feed the split difference sets of the golden-silver Wang product into the coarse-connectivity necessary condition
target: v-times-golden-silver-wang-product-full-group-is-not-fp
requires: [metallic-wang-shift-product-is-minimal-with-split-differences, fp-v-times-subshift-full-groups-force-connected-differences, v-times-ample-full-groups-are-generated-by-transpositions]
---

The notation is that of the target.

**Hypotheses of the necessary condition.**
- `Λ = Z^2` is infinite, with finite symmetric generating set `S = {±e_1, ±e_2}`. Its word metric
  is the `ℓ^1` metric, which is the metric used in
  `metallic-wang-shift-product-is-minimal-with-split-differences`.
- `X = Ω_1 × Ω_2` is a subshift of `A^(Z^2)` with `A = T_1 × T_2` finite. `Z^2` acts on it freely,
  by part 1 of `metallic-wang-shift-product-is-minimal-with-split-differences`.
- The shift convention there (`σ^k` or `(g.w)(p) = w(p - g)`) changes neither `X` nor the sets
  `Δ(u, v)`, so it matches the setting of `fp-v-times-subshift-full-groups-force-connected-differences`.

**Part 1.** Suppose `Γ ≤ F(T)` is finitely presented and contains every `t_s` and every `e_a`.
- Part 1 of `fp-v-times-subshift-full-groups-force-connected-differences` gives `m` such that
  `Δ(u, v)` is `m`-connected for all `u, v ∈ X`.
- Part 3 of `metallic-wang-shift-product-is-minimal-with-split-differences` gives `u, v ∈ X` with
  `Δ(u, v)` not `m`-connected.

This is a contradiction.

**Part 2.**
- `F(T)` contains every `t_s` and every `e_a`: each is a homeomorphism of `C × X` given locally by
  germs of `T`, on the clopen pieces `C × X`, and `[00] × [a]`, `[01] × [a]`, `[1] × [a]`,
  `C × [≠ a]`.
- By part 1, `F(T)` is not finitely presented.
- `F(T) = A(T)` by `v-times-ample-full-groups-are-generated-by-transpositions`, applied with
  `H = Z^2 ⋉ X`. This is an ample Hausdorff groupoid on the compact totally disconnected space `X`.

**Part 3.**
- P2 asserts that `A(T)` is finitely presented for every infinite finitely presented `Λ` and
  every nonempty minimal free SFT `X ⊆ A^Λ`.
- The pair `(Z^2, Ω_1 × Ω_2)` satisfies these hypotheses by part 1 of
  `metallic-wang-shift-product-is-minimal-with-split-differences`.
- By part 2, `A(T)` is not finitely presented for this pair. ∎

**Remark (injectivity).** The necessary condition needs `Γ` to be a subgroup of `F(T)`. Here
`Γ = F(T)` itself, so that is automatic.
