---
rg: 2
id: constant-bias-dkkms-selectors-put-np-in-rp-via-robust-uniqueness
kind: route
title: Apply Corollary D with P = RU-YES, the robustly unique YES inputs -- NP-hardness of (RU-YES, NO) is (P1^RU) and F_inf(SL^C, RU-YES) is (P2^RU); Lemma RU shows RU-YES carries no generic approximate kernel map of rank above l + 1, so the flip violators of Theorems O and O' are absent from the class
target: constant-bias-dkkms-selectors-put-np-in-rp
requires:
  - gap3lin-hard-with-robustly-unique-yes-solutions
  - dkkms-orientations-admit-star-lists-on-robustly-unique-inputs
  - selector-witness-hypotheses-collapse-to-selector-free-form
  - value-free-star-list-references-put-np-in-rp
---

## Step 1: the class

Let RU-YES be the class of `gap3lin-hard-with-robustly-unique-yes-solutions`:
regular Gap3Lin YES inputs satisfying (RU_(eps + gamma'/(4k), rho, r0)) with
`r0 <= l + 1` and `rho < (1 - beta0)/(12k)`. By (P1^RU), `(RU-YES, NO)` is
NP-hard under Karp reductions.

## Step 2: the structure statement

By (P2^RU) (`dkkms-orientations-admit-star-lists-on-robustly-unique-inputs`),
`F_inf(SL^C, RU-YES)` holds.

## Step 3: Corollary D

The instance hypotheses of Theorem CLV hold for regular Gap3Lin through DKKMS
in the constant-bias cell, as `value-free-star-list-references-put-np-in-rp`
records (Corollary DK^C, with the budget `L` fixed there). Corollary D
of `selector-witness-hypotheses-collapse-to-selector-free-form`, with
`P := RU-YES`, gives `sel => NP ⊆ RP`. That is the target.

## Why this class (not used logically)

`robust-uniqueness-bounds-robust-kernel-rank` (ESTABLISHED) shows two things:
* RU-YES ⊆ `P^delta_(r0)`, so (P1^RU) implies (P1^rob);
* no `delta`-approximate kernel map of rank `> r0` on RU-YES is generic.

So the J'-violator and every other flip-orientation violator lie outside the
class, and Step 2 is not refuted by any known mechanism. The two prerequisites
pull in opposite directions. A smaller class makes (P2^RU) easier and
(P1^RU) harder. Proposition C of that node shows that RU is the natural
boundary for the flip mechanism: RU fails wherever a large affine family
of far-apart near-solutions exists.
