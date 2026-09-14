---
rg: 2
id: piecewise-dyadic-level-models-give-non-uniform-growth
kind: claim
title: A zero-entropy minimal subshift with piecewise uniform level models of size 2^k at infinitely many scales has G_X of non-uniform exponential growth
distinct_from:
  substitution-subshift-elementary-groups-non-uniform-growth: that needs a constant-length-2 substitution (a conjugacy (V,T²) ≅ (X,T)); this needs only piecewise level maps and zero entropy, no self-similarity of X
  dyadic-tower-subshift-full-group-non-uniform-growth: that is about the derived topological full group [[T]]′; this is about G_X = EL_3(LC(X,F_2)⋊Z)
  matrix-decompositions-of-subshift-rings-need-divisible-unit: that is the K-theoretic necessity of 2-divisibility; this is the positive theorem at that boundary
artifacts:
  - research/artifacts/sk-growth-gx-sturmian-2026-09-14-part1.md
---

**ESTABLISHED (unreviewed; sk-growth-gx-sturmian), conditional on the import `krieger-subshift-embedding-theorem`.**

**Hypothesis (piecewise dyadic level model at scale k).** A clopen partition `X = W_1 ⊔ … ⊔ W_(2^k)` together with, for each `i`, a finite clopen partition `W_1 = ⊔_(n∈F_i) A^(i)_n` such that the sets `T^n A^(i)_n` (`n ∈ F_i`) are pairwise disjoint with union `W_i`. So `W_1` is carried onto every `W_i` by a piecewise power of `T`. Constant towers (`W_i = T^(i−1)W_1`) are the special case `F_i = {i−1}`.

**Statement.** Let `X` be an infinite minimal subshift of topological entropy 0 that admits piecewise dyadic level models at infinitely many scales `k`. Then `G_X = EL_3(LC(X,F_2) ⋊ Z)` has non-uniform exponential growth: `inf_S ω(G_X,S) = 1` over finite generating sets `S`, while every `ω(G_X,S) > 1`.

**Scope.**
- Necessity side: by Lemma K (sk-sturmian-growth part 2) and `matrix-decompositions-of-subshift-rings-need-divisible-unit`, the hypothesis forces `[1_X] ∈ 2^k K^0(X,T)`, so Sturmian subshifts are excluded.
- It contains `substitution-subshift-elementary-groups-non-uniform-growth` in the zero-entropy form, and sk-free-8 Corollary A2 (dyadic odometer factor, constant towers).
- Firewall: no example certified here of a zero-entropy minimal subshift with piecewise dyadic level models but no dyadic continuous eigenvalue. For primitive substitutions with even return lengths, Host's criterion seems to produce dyadic eigenvalues anyway (artifact part 1 §4).

Route: `piecewise-dyadic-level-models-give-non-uniform-growth-proof`.
