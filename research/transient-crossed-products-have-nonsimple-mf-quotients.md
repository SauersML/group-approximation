---
rg: 2
id: transient-crossed-products-have-nonsimple-mf-quotients
kind: claim
title: A zero-dimensional crossed product with transient points never has a simple maximal MF quotient of its elementary group
distinct_from:
  toeplitz-subshift-kazhdan-group-has-pestov-mf-quotient: that produces a nontrivial MF radical with a simple maximal MF quotient; this shows crossed products of zero-dimensional systems cannot, which is why that construction is a Toeplitz extension rather than a crossed product.
artifacts:
  - research/artifacts/un-hh-extension-toeplitz-subshift-2026-09-13.md
---

Let `X` be a compact metrizable zero-dimensional space with a homeomorphism `T`, let `Y = CR(T)`, `k = F_2` and
`n >= 4`. Suppose `X != Y`, so the MF radical `EL_n(R_X, I)` of the manuscript's `thm:core-mf-radical` is nontrivial.
Then the maximal MF quotient `EL_n(LC(Y,F_2) x| Z)` is not simple modulo its centre.

So the sandwich shape "nontrivial locally finite radical, simple maximal MF quotient" is invisible to every
zero-dimensional crossed product. It needs a ring whose defect ideal is not a transient part of the dynamics.

**Review (un-verify-3, 2026-09-13): PASS.** `thm:core-mf-radical` (tex l.1609) gives `Rad_MF(EL_n(R_X)) = K_n` for `n ≥ 4`, with elementary quotient `EL_n(R_Y)`. `X ≠ Y` makes `Y` not chain transitive, hence not minimal, so there is a nonempty closed invariant `Z ≠ Y`. `I_Z` is a nonzero proper two-sided ideal (invariance of `Z`; zero-dimensionality). `EL_n(R_Y, I_Z)·Z` is proper, because `EL_n(R_Y/I_Z)` is nontrivial and perfect. Display note: `[e_12(a), e_23(1)] = e_13(a) ≠ 1` shows nontriviality; noncentrality follows from `[e_13(a), e_32(1)] = e_12(a) ≠ 1`. `research/artifacts/un-review3-2026-09-13-part5.md` §3.
