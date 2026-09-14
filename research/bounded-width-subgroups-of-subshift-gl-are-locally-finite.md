---
rg: 2
id: bounded-width-subgroups-of-subshift-gl-are-locally-finite
kind: claim
title: A subgroup of GL_m(LC(X,F_q) ⋊ Z) whose elements have uniformly bounded u-width is locally finite
distinct_from:
  subshift-crossed-product-gl-has-no-distorted-elements: that shows single elements of sublinear width growth have finite order; this shows a whole subgroup with uniformly bounded width is locally finite
  cut-stabilizers-of-el-n-are-locally-finite-normalish: that treats the cut stabilizer, whose elements have unbounded width; this treats subgroups of bounded width, such as stabilizers of two-ended lattices
artifacts:
  - research/artifacts/sk-exact-gx-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `X` is an infinite minimal subshift with shift `T`, `F_q` a finite field, `R = LC(X,F_q) ⋊_T Z` and `m ≥ 1`.
- The width `w(g)` of `g ∈ GL_m(R)` is the largest `|k|` with a nonzero `u^k`-coefficient in some entry of `g` or `g^{-1}`.

**Theorem.** If `Γ ≤ GL_m(R)` satisfies `sup_{γ∈Γ} w(γ) < ∞`, then `Γ` is locally finite.

**Consequences.**
- The stabilizer in `G_X` of any pair of lattices at `±∞` is locally finite: `subshift-el3-two-ended-lattice-stabilizers-locally-finite`.
- The cyclic case recovers finite order for elements all of whose powers have bounded width. The no-distortion theorem proves more for single elements.

**Proof:** `bounded-width-subgroups-of-subshift-gl-locally-finite-proof`.

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived: the faithful banded representation, invariant windows U_t of dimension ≤ m(2p+1), the embedding in ∏GL(U_t), and finitely many normal subgroups of bounded index in F_k. The model tests are correct. See `research/artifacts/sk-verify-16-2026-09-13-part3.md` §6.
