---
rg: 2
id: subshift-elementary-group-lef-growth-at-least-exp-r-squared
kind: claim
title: For every infinite minimal subshift X, the LEF growth of EL_3(LC(X,F_2)⋊Z) is at least exp(c r²)
---

**OPEN.** Is L_X ≽ exp(r²) for every infinite minimal subshift X?

By `short-towers-force-large-lef-models`, it suffices to find, for all large m, a nonempty clopen W with W ∩ T^tW = ∅ for 0 < |t| ≤ 2m and |e_12(e_W)| = O(m).

## Attempts
- **Rotation factors (done, unreviewed).** `rotation-factor-subshift-lef-growth-at-least-exp-r-squared` covers every X with an irrational rotation factor in which some letter is sandwiched by an arc. The towers are {x_0 = a, x_{q_n} ≠ a}.
- **One-hole Toeplitz (done, unreviewed).** `one-hole-toeplitz-lef-growth-at-least-exp-r-squared`, with towers {y_0 ≠ y_{p_k}}.
- **Extensions (done, unreviewed).** `lef-growth-of-subshift-el-groups-is-monotone-under-factors` gives L_Y(r) ≤ L_X(Kr) for every factor Y of X. So every extension of a covered subshift is covered. Example: Thue–Morse, through period doubling (`thue-morse-elementary-group-lef-growth-is-exp-r-squared`).
- **Weakly mixing, rank one (done, unreviewed).** Chacón has no eigenvalues, but {y_0 = y_1 = 0, y_{h_n+1} = 1} isolates one position per B_{n+1}-block (`chacon-elementary-group-lef-growth-is-exp-r-squared`). The mechanism in every covered case is a letter-change test at a partial-rigidity time.
- **High complexity (done, partial).** If p_X(n) ≥ c·n⁴ for all large n, Theorem B(B2) of `subshift-elementary-group-lef-growth-complexity-bounds` already gives exp(c'r²).
- **Full cylinders (dies).** They cost O(m²) (sk-lef-growth Lemma 2), so the tower method gives only exp(cr).
- **Open range.** Complexity o(n⁴) without a letter-change test:
  - linearly recurrent primitive substitutions with several level-n blocks (Tribonacci numerics suggest short 2- and 3-letter towers, unproved);
  - zero-entropy topologically mixing minimal subshifts.

  k-letter patterns with shifts ≤ s cost O(k²s), so k = O(log m) would still give exp(cr²/log⁴r).
- **Firewall (no smaller growth from these towers).** Every covered X also has L_X ≼ exp(r²) when special factors are bounded (`rauzy-walk-bounds-lef-growth-by-special-factors`). No example with growth o(exp(r²)) is known. Any X with L_X ≼ exp(r^{2−ε}) would need every clopen set with no returns up to 2m to cost ≫ m.
