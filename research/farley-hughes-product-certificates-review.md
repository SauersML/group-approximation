---
rg: 2
id: farley-hughes-product-certificates-review
kind: claim
title: Referee review of the product-certificate addendum in 50a3370920 — singleton rectangles, total-depth address bound and residual W_d all check for products of nested factors (FH Def. 3.25, Rem. 3.27), so the 2^O(n) seed cap extends to nV, S_Σ and Bieri–Sach-type products; for Cantor-factor products such as nV the cap is vacuous, since no point is a singleton domain; the correction notes of 83369e12b2 are accurate apart from one overstatement
distinct_from:
  farley-hughes-chart-coordinates-review: that review left non-nested certificates open; this checks the lane's extension to products of nested factors.
  farley-hughes-certificates-have-prefix-chart-coordinates: that is the lane node whose product addendum is reviewed here.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the addendum "product certificates" in 50a3370920, and a
spot-check of 83369e12b2).**
Read at source in FH arXiv:2010.08035v1:
- Def. 3.25: the product action `(s_1, …, s_n)(x_1, …, x_n) = (s_1(x_1), …, s_n(x_n))`;
- Remark 3.27: `𝒟⁺ = {D_1 × ⋯ × D_n}`;
- Def. 4.32 and Ex. 8.5.

## Verdict: PASS for products of nested factors

1. **Singleton rectangles.** The argument is correct.
   - *Refinement.* Replace a factor `D_i` by `D_i ∩ E_i`. That is a factor domain, by nesting, and the rest
     `D_1 × ⋯ × (D_i ∖ E_i) × ⋯ × D_k` is a finite union of rectangles, by factor finite complementation (FH
     Remark 3.15).
   - *Two nontrivial factors.* For each coordinate `l`, move `x` in some other nontrivial coordinate `m ≠ l`. That
     gives a fixed point of `D ∖ {x}` agreeing with `x` at `l`, so `s(x) = x`.
   - *One nontrivial factor.* The nested contradiction runs in that factor. It needs `z_i ∉ D_i`, which holds
     because `z ∉ D` and `z_j = x_j` for `j ≠ i`.
   - *Hypotheses.* The argument uses each `X_i` a finite union of factor domains (FH Conv. 3.9 per factor) and
     factor domains that separate points. The addendum assumes both.
2. **Total depth.** Factor S-maps preserve relative factor depth (FH Prop. 3.24 in each nested factor), so product
   S-maps preserve relative total depth additively.
   - A chart maps onto a proper sub-rectangle, adding at least 1 to `δ`.
   - Structure maps are tuples (maximal structure, Def. 4.32), so `H_τ` preserves `δ`, and generators change `δ`
     boundedly.
   - So every chart address of `y` has length `≤ δ({y})`, and the recursion of item 4 gives `2^(O(n))`, as in
     the nested case.
3. **Residually `W_d`.** `H_τ` embeds in the product of the factor tree automorphism groups, and a product of
   residually-`W_d` groups is residually `W_d` for the largest degree.

## Two scope notes

- **Cantor-factor products have no singleton domains.** Examples are `nV` (FH Ex. 3.31) and Brin's patterns. Item 1
  then shows that such certificates cannot contain a transposition of two points, so they never certify a seed full
  group. There the cap is vacuous, not violated.
- **Where the extension has content.** Products with vertex-tree factors, such as FH Ex. 8.5 with barred entries
  (`S_(n̄)`, the `QV`-type factors), and Bieri–Sach-type products of Houghton semigroups (FH Ex. 3.34).
- **Still open.** Certificates whose domains are neither nested nor products of nested factors. No FH application
  of this kind is known.

## Spot-check of 83369e12b2

- **Accurate.** The credit and the residually-`W_d` wording are accurate in both
  `gq-bh-bh-invent-03-seed-tower-gate1-state` §6 and `decidable-residually-wd-groups-embed-in-lift-presented-hosts`.
  The product addendum is correctly marked "not reviewed". It is now reviewed here.
- **One overstatement.** The second node states as settled that `WP(Γ_S)` "is exponential over the word problems
  of its structure groups". That is item 4(b), which dda7d68b92 graded **a plausible sketch, not checked in
  detail**. It should say so.

## Lesson for general BH

- **What the depth argument needs.** Only that structure maps preserve an additive, integer-valued depth, and
  that charts strictly increase it. Products of nested factors have this, with total depth.
- **So** any certificate built from ultrametric pieces by products caps seeds at `2^(O(n))`.
