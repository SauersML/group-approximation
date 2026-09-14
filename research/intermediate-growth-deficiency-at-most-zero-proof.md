---
rg: 2
id: intermediate-growth-deficiency-at-most-zero-proof
kind: route
title: Deficiency one gives an aspherical Euler-characteristic-zero complex whose indicable kernels are free by Kochloukova
target: intermediate-growth-groups-have-deficiency-at-most-zero
requires:
  - fp-subexponential-growth-forces-sqrt-mod-p-betti-bound
  - finite-2-complex-with-zero-second-l2-betti-is-aspherical
  - amenable-normalish-kills-l2-betti-bounded-cohomology
  - intermediate-growth-z-quotient-kernels-fg-intermediate
  - kochloukova-euler-zero-cyclic-quotient-kernels-have-cd-drop
artifacts:
  - research/artifacts/hl-fp-intermediate-growth-2026-09-14.md
---

Let `G` have intermediate growth. Then `G` is infinite.

**Item 1.**
1. Let `U ≤ G` have index `j < ∞`.
   - The `j`-sheeted cover `Y_U` of `Y` is a finite 2-dimensional `K(U,1)` with
     `χ(Y_U) = jχ(Y) = 0`.
   - `U` has intermediate growth, since finite-index subgroups have equivalent growth functions.
2. Suppose `U/[U,U]` is infinite. Then `H₁(U; Z)` has a free summand, so there is a surjection
   `φ: U → Z`. Its kernel `N` is finitely generated of intermediate growth, by
   `intermediate-growth-z-quotient-kernels-fg-intermediate` (applied to `U`, which is covered by its
   finite-index clause).
3. By `kochloukova-euler-zero-cyclic-quotient-kernels-have-cd-drop` (the consequence for `n = 2`,
   applied to `U` and `Y_U`), `N` is free.
4. A free group of rank at most 1 has polynomial growth. A free group of rank at least 2 has
   exponential growth: the `2ⁿ` positive words of length `n` in two free generators are distinct.
   Either way this contradicts step 2, so `U/[U,U]` is finite.

**Item 2.**
5. If `|X| − |R| ≥ 2`, item 1 of `fp-subexponential-growth-forces-sqrt-mod-p-betti-bound` gives a
   contradiction.
6. Let `|X| − |R| = 1`, and let `K` be the presentation complex. Then `χ(K) = 1 − |X| + |R| = 0`.
7. **Amenability.**
   - Fix a finite symmetric generating set and its balls `B(n)`, and let `ε > 0`.
   - If `|B(n+1)| ≥ (1 + ε)|B(n)|` held for all large `n`, growth would be exponential. So there are
     infinitely many `n` with `|B(n+1) \ B(n)| < ε|B(n)|`.
   - For each generator `s`, `sB(n) ⊆ B(n+1)` and `|sB(n)| = |B(n)|`, so
     `|sB(n) △ B(n)| < 2ε|B(n)|`.
   - These balls form a Følner sequence, so `G` is amenable by Følner's criterion (standard).
8. **Vanishing.** `G` is an infinite amenable group, and it is an amenable normalish subgroup of
   itself: for all `t₁,…,t_n` the intersection `⋂ t_iGt_i⁻¹ = G` is infinite. By
   `amenable-normalish-kills-l2-betti-bounded-cohomology`, `b₁^(2)(G) = 0`.
9. **Asphericity.** So `χ(K) + b₁^(2)(G) = 0` with `G` infinite, and `K` is aspherical by
   `finite-2-complex-with-zero-second-l2-betti-is-aspherical`. It is a finite 2-dimensional
   `K(G,1)` with `χ = 0`.
10. **Conclusion.** `H₁(G; Q)` is the cokernel of the map `Q^{|R|} → Q^{|X|}` given by relator
    exponent sums. So `dim H₁(G; Q) ≥ |X| − |R| = 1`, and `G/[G,G]` is infinite. This contradicts
    item 1 with `U = G`.
