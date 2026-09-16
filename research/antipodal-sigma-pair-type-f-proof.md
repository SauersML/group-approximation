---
rg: 2
id: antipodal-sigma-pair-type-f-proof
kind: route
title: "Openness and Renz's kernel criterion give a fibration with FP fibre; the ascending HNN Euler class vanishes"
target: f-infinity-fcd-group-with-antipodal-sigma-pair-is-type-f
requires: [ascending-hnn-of-fp-group-has-zero-k0-euler-class]
artifacts:
  - research/artifacts/zaremsky-1-21-fibering-and-retracts-2026-09-16.md
---

Literature imports:

- **Homological invariants.** For `G` of type `FP_m`, `Σ^m(G;Z)` is open in
  `S(G)`. For a discrete character `χ`, `ker χ` is of type `FP_m` iff
  `[χ], [−χ] ∈ Σ^m(G;Z)`. Source: R. Bieri and B. Renz, Comment. Math. Helv.
  63 (1988), recalled. It is the same import as the established
  `nonzero-euler-characteristic-blocks-symmetric-sigma-proof`.
- **Homotopical invariants.** For `G` of type `F_m`, `Σ^m(G)` is open, and
  `ker χ` is of type `F_m` iff `[±χ] ∈ Σ^m(G)` (Renz, Satz C). This is quoted
  from M. Ershov and M. C. B. Zaremsky, arXiv:2505.18826, §2 and Theorem 2.3,
  fetched and read 2026-09-16.

Also `Σ^∞(G) ⊆ Σ^m(G) ⊆ Σ^d(G) ⊆ Σ^d(G;Z)` for `m ≥ d`. So each listed
hypothesis implies the homological one, and the homotopical case can be run
with the verified import alone.

Proof:

1. **Open set.** `U = Σ^d(G;Z) ∩ −Σ^d(G;Z)` is nonempty and open, since the
   antipodal map is a homeomorphism of `S(G)`.
2. **Discrete character.** `G` is finitely generated, so
   `Hom(G,R) = Hom(G,Q) ⊗ R`, and rational rays are dense in `S(G)`. Choose
   `[χ] ∈ U` with `χ(G) ⊆ Q`, and rescale so that `χ(G) = Z`.
3. **Kernel `FP_d`.** By the kernel criterion, `N = ker χ` is of type `FP_d`.
4. **Kernel FP.** `cd N ≤ cd G = d`. In a free resolution `F_* → Z` over `ZN`
   with `F_0, …, F_d` f.g., the kernel `K = ker(F_{d−1} → F_{d−2})` satisfies
   `Ext^1(K,M) = H^{d+1}(N;M) = 0` for all `M`. So `K` is projective. It is
   finitely generated as the image of `F_d`. So `N` is of type FP.
5. **`G` is finitely presented**, since it is of type `F_∞`.
6. **Conclusion.** `χ` is onto `Z` with FP kernel and `G` is finitely
   presented. The corollary of
   `ascending-hnn-of-fp-group-has-zero-k0-euler-class` (`G ≅ N ⋊ Z = N*_α`)
   gives: `G` is of type F and `χ_G = 0`. The fibration is `χ` itself. QED

For a counterexample `G`, contraposition gives `U = ∅`.

If an automorphism `α` of `G` acts as `−1` on `Hom(G,R)`, then
`Aut(G)`-invariance of the invariants (arXiv:2505.18826 §2, homotopical, same
proof homologically) gives `Σ^d(G;Z) = −Σ^d(G;Z)`, hence `Σ^d(G;Z) = U = ∅`.
