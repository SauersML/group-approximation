---
rg: 2
id: minimal-cantor-crossed-products-have-internal-cancellation
kind: claim
title: LC(X,F) ⋊ Z for a minimal Cantor system has internal cancellation; idempotents are similar iff equivalent, iff their clopen models are full-group equivalent
distinct_from:
  minimal-cantor-crossed-product-has-stable-rank-at-most-two: that asks for Bass stable rank ≤ 2 (or 1) for all unimodular rows; this proves internal cancellation of idempotents, which for exchange rings is equivalent to stable rank one.
  subshift-el-transvection-conjugacy-full-group-equivalence: that is about conjugacy of root transvections in the group G_X; this is about equivalence of idempotents in the ring, proved through a Birkhoff-sum bound and Gottschalk–Hedlund.
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `(X,T)` be a minimal homeomorphism of the Cantor set, `F` a field, `R = LC(X,F) ⋊_T Z`.
1. **Cancellation.** If `e, f ∈ R` are idempotents with `eR ≅ fR`, then `(1−e)R ≅ (1−f)R`. So `e` and `f` are similar.
2. **Clopen models.** For clopen `W, W′`, the following are equivalent:
   - `e_WR ≅ e_{W′}R`;
   - `1_W − 1_{W′} = g∘T − g` for some `g ∈ C(X,Z)`;
   - `γW = W′` for some `γ` in the topological full group `[[T]]`.

**Proof outline** (artifact §4).
- An equivalence `x ∈ e_WRe_{W′}` of propagation `w` injects `W′`-coordinates of an interval (shrunk by `w`) into `W`-coordinates, so the Birkhoff sums of `1_W − 1_{W′}` along an orbit are bounded by `2w`.
- Gottschalk–Hedlund gives a continuous, integer-valued transfer function.
- Kakutani–Rokhlin towers over a clopen set where it is constant have equally many `W`- and `W′`-levels. A level permutation `γ ∈ [[T]]` sends `W` to `W′` and `X∖W` to `X∖W′`, and its unit `w_γ` conjugates `e_{X∖W}` to `e_{X∖W′}`.
- General idempotents reduce to clopen ones by `cantor-crossed-product-idempotents-similar-to-clopen-ones`.

**Review (sk-verify-16, 2026-09-13): PASS**, conditional on the Gottschalk–Hedlund import (secondary quotation). Re-derived: the Birkhoff bound 2w from an equivalence of propagation w; an integer-valued continuous transfer function; level matching over first-return towers; w_γ e_V w_γ⁻¹ = e_{γV}; cancellation via the idempotent classification. Wording: rename the base point (x_0) to avoid a clash with the equivalence element x. See `research/artifacts/sk-verify-16-2026-09-13-part4.md` §2.
