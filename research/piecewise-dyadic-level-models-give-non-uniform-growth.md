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

## Review
- **sk-verify-21 PASS, conditional on `krieger-subshift-embedding-theorem` as stated (2026-09-14, `research/artifacts/sk-verify-21-2026-09-14.md` §1):** re-derived by hand:
  - the matrix units `ε_ij = s_i s′_j`: disjointness of the `T^nA^(i)_n` kills the cross terms, and `s′_j = s′_j e_(W_j)`, `s_i = e_(W_i)s_i`;
  - the corner isomorphism `LC(W,F_2) ⋊_(T_W) Z ≅ e_WRe_W`: covariance `v f v′ = f∘T_W^(−1)`, `v^m = Σ_j e_(D_(m,j))u^j` with the `D_(m,j)` disjoint in `m`, then surjectivity and injectivity;
  - return-word coding, `h_top(T_W) = 0` by Kakutani, full support and Abramov, then Krieger and generation by `v, v^(−1), e_U`;
  - Lemma 4, Lemma 0, and (T) ⇒ non-amenable ⇒ `ω > 1`.
  - Theorem B is applied to rings `A_k` that change with `k`. This needs `C`, `β` and the threshold on `n` to be independent of `A`, as recorded in sk-verify-14 part 4 l.63.
  - The necessity bullet holds directly: `[χ_X] = 2^k[χ_(W_1)]`.
