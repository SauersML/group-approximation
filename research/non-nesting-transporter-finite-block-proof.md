---
rg: 2
id: non-nesting-transporter-finite-block-proof
kind: route
title: Pull the comparison into the finite block group of the two charts and count ranks on the block module
target: non-nesting-transporters-cannot-install-chart-comparison
requires: []
artifacts:
  - research/artifacts/kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md
---

Complete direct proof.

1. **The block group is finite.** An element of `K` is a sum of monomials
   `S[c]T[c']` with `c, c'` in `Lambda`, plus the projection onto the complement of
   `[0]`. It sends `c.w` to a combination of `c'.w` with the same tail `w`, and fixes
   points outside `[0]`. The same holds for `K' = h^-1 K h` on the leaves
   `h^-1 Lambda`, since conjugating by a prefix permutation relabels prefixes and
   keeps tails. If no cone of one family properly nests a cone of the other,
   `U = Lambda union h^-1 Lambda` is prefix-free. Each point under `[U]` is uniquely
   `c.w` with `c in U`, and both groups act by `|U| x |U|` block matrices independent
   of `w`, fixing all other points. The action of `Q` on the boundary module is
   faithful, so `H' = <K, K'>` embeds in `GL_|U|(F_2)` and is finite.
2. **Factor the comparison.** `P_0 [h] f_0 = [h] P' f_0` with `P' = h^-1 P_0 h in F_2[K']`.
   If `L P_0 [h] f_0 = f_0`, then `Y = f_0 E_(H')(L h) P'` lies in `f_0 F_2[H'] P'` and satisfies
   `Y (P' f_0) = f_0`, because `P' f_0` and `f_0` lie in `F_2[H']` and `E_(H')` is a bimodule
   map.
3. **Isomorphism in the finite group algebra.** Left multiplication by `P' f_0` embeds
   `f_0 F_2[H']` as a direct summand of `P' F_2[H']`. Both have dimension `[H' : K] * 32`
   (`|K'| = |K|`, and equal chart ranks), so the embedding is onto, and the two
   projective modules are isomorphic.
4. **Rank count on the block module.** Isomorphic projectives mean the idempotents
   are Murray--von Neumann equivalent, `f_0 = x y` and `P' = y x`. Then `f_0 M` and
   `P' M` are isomorphic through `y` and `x` for every left `H'`-module `M`, so
   `dim f_0 M = dim P' M`. Take `M = F_2^U`. As a
   `K`-module it is the natural 4-dimensional module plus trivial coordinates. `f_0`
   acts as zero on both: the half-corner artifact records that `f_+` and the
   central block `E` vanish on the natural module, and the reduced projectors lie in
   the nontrivial central block, which kills trivial coordinates. So `dim f_0 M = 0`.
   As a `K'`-module, `M` is the natural module of `K'` plus trivial coordinates. `P'`
   acts there as `P_0` does on the natural module, namely `diag(0,0,1,1)`, so
   `dim P' M = 2`. This contradicts step 3. `square`

For `f_+, P` the same count applies. `f_+` is zero on the natural module and `P` has
rank 2 there, and both have chart rank 40.
