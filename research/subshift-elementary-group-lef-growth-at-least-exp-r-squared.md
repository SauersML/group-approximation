---
rg: 2
id: subshift-elementary-group-lef-growth-at-least-exp-r-squared
kind: claim
title: For every infinite minimal subshift X, the LEF growth of EL_3(LC(X,F_2)⋊Z) is at least exp(c r²)
---

**OPEN.** Is L_X ≽ exp(r²) for every infinite minimal subshift X?

By `short-towers-force-large-lef-models`, it suffices to find, for all large m, a nonempty clopen W with W ∩ T^tW = ∅ for 0 < |t| ≤ 2m and |e_12(e_W)| = O(m).

## Attempts
- **Rotation factors (done).** `rotation-factor-subshift-lef-growth-at-least-exp-r-squared` covers every X with an irrational rotation factor in which some letter is sandwiched by an arc. The sets are {x_0 = a, x_{q_n} ≠ a}.
- **Positive complexity growth (done, partial).** If p_X(n) ≥ c·n⁴ for all large n, then Theorem B(B2) of `subshift-elementary-group-lef-growth-complexity-bounds` already gives exp(c'r²). The open range is p_X(n) = o(n⁴) without a rotation factor.
- **Full cylinders (dies).** A cylinder of length ~m has no short returns once m is large, but costs O(m²) (sk-lef-growth Lemma 2). The tower method then gives only exp(cr).
- **Odometer factors (dies for the letter-change set).** A letter that factors through a clopen set of an odometer is invariant under large periods, so {x_0 = a, x_{p_k} ≠ a} is empty. Toeplitz holes give a different set, treated in `research/artifacts/sk-lef-growth-all-towers-2026-09-13-part1.md` §4 and part 2.
- **Weakly mixing systems (open).** Chacón has no eigenvalues. Whether a bounded number of letter conditions over span O(m) can have no returns up to 2m is being tested numerically by lane sk-lef-growth-all (part 2).
