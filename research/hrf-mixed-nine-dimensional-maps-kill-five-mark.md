---
rg: 2
id: hrf-mixed-nine-dimensional-maps-kill-five-mark
kind: claim
title: Every representation of a nonzero pinned five-twist in dimension at most nine over any field kills its central mark
distinct_from:
  hrf-amplified-sym4-five-twists-have-no-detectors: that treats arbitrary dimension in one characteristic-19 isotypic family with scalar mark; this treats all representations in dimensions at most nine in every characteristic and permits nonscalar marks
  hrf-mixed-detectors-have-balanced-edge-spectra: that gives necessary spectral and composition constraints; this combines those constraints with an elementary root-subgroup orbit bound to exclude every low-dimensional representation
artifacts:
  - research/artifacts/hrf-mixed-nine-dimensional-obstruction-2026-09-20.md
---

Let `Lambda_d` have three canonical `PSL_2(F_19)` vertices, with
triangle edges pinned by the classes of `[[2,11],[16,3]]`,
`[[5,11],[4,9]]`, and `[[6,15],[12,8]]`, and relations
`Z` central, `Z^5=1`, `s_i(xij)=Z^(dij)s_j(xij)` for a nonzero
triple `d in F_5^3`.

For every field `K`, every `1<=n<=9`, and every homomorphism
`f:Lambda_d -> GL_n(K)`, one has `f(Z)=I_n`. No scalar-mark or
semisimplicity hypothesis is imposed.

In particular no actual finite linear or unitary realization in
degree five detects the mark. This does not classify abstract
central extensions of projective groups without a separate lifting
argument, and does not exclude larger-degree finite detectors.

Proof: [[hrf-mixed-nine-dimensional-maps-kill-five-mark-proof]].
