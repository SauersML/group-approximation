---
rg: 2
id: one-sided-defect-ideal-dies-in-linear-images-of-el
kind: claim
title: For any unital ring with ts=1, every finite or linear image of EL_N(R), N>=4, kills E_N(R, ReR) for e=1-st, with no property (T) or finite generation
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that is the exact MF-radical statement for defects of finite additive order, through property (T); this is the finite and linear target statement for every defect, with no (T).
  simple-dedekind-infinite-ring-elementary-full-mf-radical: that kills MF images for simple non-directly-finite rings; this kills finite and linear images for arbitrary rings, on the defect ideal only.
  finitary-linear-extension-kazhdan-defect-kills-kernel: that is the MF-level criterion over F_2, where a compressed Kazhdan subgroup of a finitary linear extension kills the whole finitary kernel through property (T); this concerns only finite and linear targets, over an arbitrary unital ring, and needs no (T).
artifacts:
  - research/artifacts/un-open-8-target-agnostic-compression-2026-09-13.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED, unreviewed.** Let `R` be a unital ring, `s,t in R` with `ts = 1`, `e = 1 - st`, and `N >= 4`.
- Every homomorphism from `EL_N(R)` to a finite group, or to `GL_d(K)` for a field `K`, is trivial on the relative
  elementary subgroup `E_N(R, ReR)`.
- If `R` is simple and not directly finite, every such homomorphism is trivial.

**Calibration.**
- **Toeplitz and Jacobson rings.** For `k<s,t : ts=1>` and `Z<s,t : ts=1>`, `ReR = M_fin`. So linear images kill
  the finitary part, and `EL_N(k[z,z^-1])` survives. At the MF level the integral case is undecided
  (`integral-jacobson-mf-radical-is-all-or-nothing`). So property (T) is needed only at the MF level.
- **Pestov ring.** `LC(X,F_q) ⋊ Z` is directly finite, so the statement is vacuous there.

**Review (un-verify, 2026-09-13): PASS.** The rank-four cell of tex Lemma l.866 re-derived for every unital ring with `ts = 1`: the `u_i` block `[[s,e],[0,t]]`, `u = u_3u_2u_1` with last column `(e, et, et², t³)`, `u e_ij(a) = e_ij(sat) u`, `c = [e_41(e), e_14(t)] = diag(1,1,1,1+et)`, `uc = e_12(e)u = u + et E_14`; then Lemma C and the Steinberg spread. See `research/artifacts/un-review-2026-09-13-part8.md` §3.

**Credit and scope (un-verify, 2026-09-13, subsumption correction).** The statement is the composition of the printed rank-four compression cell (`non_mf_groups_exist.tex` Lemma `lem:ring-compression-cell`, l.866) with the older Lean-certified `compression-defect-dies-in-finite-dimensions` (finite targets through the regular representation); no older node states the composition for arbitrary unital rings, so what is new is that composition and the Steinberg spread to `E_N(R, ReR)` without property (T). Specific instances were already recorded: `binary-jacobson-elementary-mark-is-finite-quotient-invisible` and `binary-jacobson-core-is-weakly-sofic-with-fd-head-radical`. See `research/artifacts/un-review-2026-09-13-part8.md` §5.
