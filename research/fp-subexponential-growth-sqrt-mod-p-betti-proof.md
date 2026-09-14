---
rg: 2
id: fp-subexponential-growth-sqrt-mod-p-betti-proof
kind: route
title: Count generators and relators of covering presentations and apply the Golod–Shafarevich test
target: fp-subexponential-growth-forces-sqrt-mod-p-betti-bound
requires:
  - golod-shafarevich-deficiency-test-and-exponential-growth
artifacts:
  - research/artifacts/hl-fp-intermediate-growth-2026-09-14.md
---

1. **Covering presentations.**
   - Let `K` be the presentation complex of `⟨X | R⟩`: one vertex, `|X|` edges, `|R|` 2-cells, and
     `π₁(K) = G`.
   - A subgroup `U` of index `j` is the fundamental group of the connected `j`-sheeted cover `K_U`,
     which has `j` vertices, `j|X|` edges and `j|R|` 2-cells.
   - Collapse a maximal tree of the 1-skeleton (`j − 1` edges). The result is a presentation complex
     for `U` with one vertex, `j|X| − j + 1` edges and `j|R|` 2-cells.
   - This gives a presentation `U = ⟨X_U | R_U⟩` with `|X_U| = j(|X| − 1) + 1` and `|R_U| = j|R|`.
2. **The test.** Put `d = d_p(U)` and assume `d ≥ 2`.
   - The inequality `|R_U| < d²/4 − d + |X_U|` reads `j|R| < d²/4 − d + j(|X| − 1) + 1`.
   - Equivalently, `4jc < (d − 2)²` with `c = |R| − |X| + 1`.
   - If it holds, `U` is Golod–Shafarevich (item 1 of
     `golod-shafarevich-deficiency-test-and-exponential-growth`) and so has exponential growth
     (item 2).
3. **Growth passes to `G`.**
   - Let `L = max_{s ∈ X_U} |s|_X`, the length in `G` of the generators of `U`. Words of length `n`
     in `X_U` have length at most `Ln` in `X`, so `|B_G(Ln)| ≥ |B_U(n)|`.
   - If `|B_U(n)| ≥ λⁿ` with `λ > 1` for large `n`, then `|B_G(Ln)|^{1/(Ln)} ≥ λ^{1/L} > 1`, and `G`
     has exponential growth.
   - `G` has subexponential growth, so `(d − 2)² ≤ 4jc` whenever `d ≥ 2`. This is item 2.
4. **Item 1.** Suppose `c < 0`, i.e. `|X| − |R| ≥ 2`, and take `U = G`, `j = 1`.
   - `H₁(G; F_p)` is the cokernel of the map `F_p^{|R|} → F_p^{|X|}` sending each relator to its
     exponent-sum vector mod `p`. So `d_p(G) ≥ |X| − |R| ≥ 2`.
   - Then `(d_p(G) − 2)² ≥ 0 > 4c`, contradicting item 2 for `U = G`.
5. **Item 3.** With `c = 0`, item 2 gives `(d − 2)² ≤ 0`, so `d = 2` whenever `d ≥ 2`.
