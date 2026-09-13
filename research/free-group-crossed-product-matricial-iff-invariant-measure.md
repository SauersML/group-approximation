---
rg: 2
id: free-group-crossed-product-matricial-iff-invariant-measure
kind: claim
title: For minimal topologically free Cantor actions of free groups, the crossed product is matricial exactly when an invariant probability measure exists
distinct_from:
  residually-finite-actions-give-matricial-crossed-products: that is the sufficiency theorem for any group; this is the ring-level Tarski dichotomy for free groups, where measure, residual finiteness, rank functions and matricial embeddings all coincide.
  matricial-steinberg-algebras-have-invariant-measures: that is the necessary condition for every ample groupoid; this closes the loop for free groups.
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `F_r` (`r ∈ N ∪ {∞}`) act minimally and topologically freely on the
Cantor set `X`, `k` a field, and `R = LC(X,k) ⋊ F_r`. The following are equivalent:
- (i) `X` carries an `F_r`-invariant Borel probability measure;
- (ii) the action is residually finite;
- (iii) `R` embeds unitally and injectively in some `∏_ω M_(N_n)(k)`;
- (iv) `R` admits a unital homomorphism into some `∏_ω M_(N_n)(k)`;
- (v) `R` carries a unital Sylvester matrix rank function.

**Scope.**
- When (i) fails, `R` has no rank function at all. Two cases:
  - paradoxical actions such as `F_2 ↷ ∂F_2`, on the non-MF side;
  - measure-free actions, e.g. the measure-free Boldrini–Prasad actions without comparison. (Review note, 2026-09-13: without
    an invariant measure, `no-invariant-measure-steinberg-elementary-no-mf-quotient` (unreviewed) places these on the
    non-MF side from some rank on, not in the middle ground.)
- The claim is about rings only. The approximation type of `EL_n(R)` when (i) fails is not addressed.

Route: `free-group-crossed-product-matricial-iff-invariant-measure-proof`.

**Review (un-verify-measure, 2026-09-13): PASS, with a scope-wording fix.** Proof chain re-derived with the Kerr–Nowak primary; the Boldrini–Prasad scope bullet corrected. See `research/artifacts/un-review-measure-2026-09-13-part1.md` §M5.
