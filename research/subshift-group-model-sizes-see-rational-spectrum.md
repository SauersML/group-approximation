---
rg: 2
id: subshift-group-model-sizes-see-rational-spectrum
kind: claim
title: The sizes of ring-type finite simple approximants SL_3N(F_2) of G_X are the multiples of the orders of the finite cyclic factors of X
distinct_from:
  strong-word-graphs-give-short-primitive-periodic-models: that gives SOME primitive period between p_X(r+1) and b_X(r); this determines EXACTLY which large periods occur (the multiples of the word-graph period) and shows the constraint is forced on every ring model.
  four-regular-simple-expander-limits-encode-word-graphs: that describes which marked groups are limits of the family as periods grow; this describes along which sequences of sizes N_k a fixed G_X is a limit, through the rational spectrum of X.
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite subshift with strongly connected word graphs (e.g. minimal),
`R_X = LC(X,F_2) ⋊ Z`, and `G_X = EL_3(R_X)` with the elementary marking. Let `g_r` be the period (gcd of closed-walk
lengths) of the word graph at level `r`.

1. `g_r | g_(r+1)`, and `m | g_r` for large `r` iff `X` has a cyclic factor of order `m`, i.e. iff `e^(2πi/m)` is a
   continuous eigenvalue.
2. **Necessity.** A ring model `F → M_N(F_2)` of `R_X` through degree `2r+1`, with `r` large enough that a cyclic
   factor of order `m` is visible at level `r`, forces `m | N`: conjugate orthogonal idempotents have equal rank.
3. **Sufficiency.** For all large `N ≡ 0 mod g_r` there is a primitive cyclic word of length `N` with the same
   `(r+1)`-language as `X`. The proof is a covering closed walk plus a Perron–Frobenius count against proper powers.
4. **Corollary.** Let `N_k → ∞`. There are ring-type markings with `(SL_(3N_k)(F_2), markings) → (G_X, marking)` iff
   every finite cyclic factor order of `X` eventually divides `N_k`. So `G_X` is the limit of the FULL sequence
   `SL_(3N)(F_2)`, `N → ∞`, iff `X` is totally minimal.

Examples:
- Sturmian and Fibonacci subshifts: every `N → ∞`.
- Thue–Morse: only along `N_k` with `2^n | N_k` eventually for each `n`.
- Toeplitz: only along multiples of the periods.

Open: whether arbitrary markings force the same divisibility. See
`subshift-group-finite-simple-shadows-are-ring-models`. A yes would make the rational spectrum an isomorphism invariant
of `G_X`.

Route: `subshift-group-model-sizes-see-rational-spectrum-proof`.
