---
rg: 2
id: minimal-set-complement-ideal-is-ultramatricial
kind: claim
title: If Y contains every minimal subset of X, the ideal I_Y of LC(X,F_2)⋊Z is a union of finite matrix subrings over F_2, so its congruence kernels are elementary and locally finite
distinct_from:
  biasymptotic-subshift-complement-ideal-is-ultramatricial: that assumes the limit sets of points outside Y lie in Y; this assumes only that Y contains every minimal subset of X, which covers orbit closures of recurrent points
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

**ESTABLISHED (unreviewed)** via `minimal-set-complement-ideal-ultramatricial-proof`.

Let X ⊆ A^Z be a subshift, R_X = LC(X,F_2) ⋊ Z, and Y ⊆ X closed invariant containing every minimal subset of X. Let I_Y be the ideal of elements whose coefficients vanish on Y.
- Every finite subset of I_Y lies in a subring B ⊆ I_Y with a unit e_B and B ≅ ∏_i M_{k_i}(F_2).
- So for every n ≥ 2, GL_n(R_X, I_Y) = E_n(I_Y), and this group is locally finite.

Over a recurrent point x ∉ Y the limit-set hypothesis of `biasymptotic-subshift-complement-ideal-is-ultramatricial` fails, because x ∈ ω(x). This claim still applies.
