---
rg: 2
id: fp-intermediate-growth-witness-exclusions-proof
kind: route
title: Assemble the cover, automorphism, gap and endomorphic presentation constraints on a finitely presented intermediate growth group
target: fp-intermediate-growth-witness-exclusions
requires:
  - fp-covers-of-grigorchuk-groups-are-large
  - grigorchuk-group-is-a-normal-subgroup-of-no-fp-group
  - residually-nilpotent-groups-below-exp-sqrt-growth-are-polynomial
  - fg-kernel-of-fp-onto-z-has-ascending-finite-l-presentation
  - intermediate-growth-z-quotient-kernels-fg-intermediate
---

1. Suppose `G ↠ H` with `H` a finitely generated cover of `𝔊`, `𝔅`, or `G_ω` (`ω ∈ Ω₊`). Then
   `G` is a finitely presented cover of `H`, so `G` is large (`fp-covers-of-grigorchuk-groups-are-large`,
   item 4) and contains a free subgroup `⟨u, v⟩ ≅ F₂`. With `L = max(|u|, |v|)`, the `2ⁿ` positive
   words of length `n` in `u, v` are distinct elements of word length at most `Ln`, so
   `γ_G(Ln) ≥ 2ⁿ` and `G` has exponential growth, a contradiction.
2. `grigorchuk-group-is-a-normal-subgroup-of-no-fp-group`.
3. If `γ_G(n) ≺ e^{√n}` and `G` is residually nilpotent, `G` has polynomial growth
   (`residually-nilpotent-groups-below-exp-sqrt-growth-are-polynomial`), contradicting intermediate
   growth.
4. The kernel `H` is finitely generated of intermediate growth
   (`intermediate-growth-z-quotient-kernels-fg-intermediate`). The quotient `ℤ` is free, so the
   epimorphism splits and `G ≅ H ⋊ ℤ`. Since `H` is a finitely generated normal subgroup of the
   finitely presented `G` with cyclic quotient, `fg-kernel-of-fp-onto-z-has-ascending-finite-l-presentation`
   gives the endomorphic presentation with automorphism-inducing endomorphisms.
